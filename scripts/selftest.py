#!/usr/bin/env python3
"""Local regression suite; can also run inside the pinned verifier container."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TASK = ROOT/'task'
VERIFIER = Path(os.environ.get('VERIFIER_ROOT', TASK/'tests/verifier')).resolve()
sys.path.insert(0, str(VERIFIER))
import verify
import spec
import rust_symbolic


def expect(condition, detail):
    if not condition: raise AssertionError(detail)


def main():
    ref = (TASK/'solution/src/lib.rs').read_text()
    prefix = ref.split('pub fn authorize')[0]
    signature = 'pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> '
    def patch(body): return prefix+signature+'{'+body+'}\n'
    variants = {
      'checked': ref,
      'glm_cfg_test': (ROOT/'scripts/fixtures/glm-5.3-flash/submission/src/lib.rs').read_text(),
      'match': patch('let total = match amount.checked_add(fee) { Some(x) => x, None => return None }; if total <= balance { Some(Authorization { total_debit: total }) } else { None }'),
      'if_let': patch('if let Some(total) = amount.checked_add(fee) { if total > balance { return None; } Some(Authorization { total_debit: total }) } else { None }'),
      'wide': patch('let total = (amount as u128) + (fee as u128); if total <= balance as u128 { Some(Authorization { total_debit: total as u64 }) } else { None }'),
      'subtraction': patch('if amount > balance { return None; } if fee > balance - amount { return None; } Some(Authorization { total_debit: amount + fee })'),
      'checked_sub': patch('let available = balance.checked_sub(amount)?; if fee > available { return None; } Some(Authorization { total_debit: amount + fee })'),
      'short_circuit': patch('if amount > balance || fee > balance - amount { return None; } Some(Authorization {total_debit: amount + fee})'),
      'shadowing': patch('let total = amount.checked_add(fee)?; let amount = total; if amount <= balance {Some(Authorization {total_debit: amount})} else {None}'),
      'wide_from': patch('let total = u128::from(amount) + u128::from(fee); if total <= u128::from(balance) {Some(Authorization {total_debit: total as u64})} else {None}'),
      'guarded_wrapping': patch('if amount > u64::MAX - fee { return None; } let total = amount.wrapping_add(fee); (total <= balance).then_some(Authorization {total_debit: total})'),
    }
    rejects = {
      'wrapping': patch('let total = amount.wrapping_add(fee); (total <= balance).then_some(Authorization {total_debit: total})'),
      'always_none': patch('None'),
      'wrong_total': patch('let total = amount.checked_add(fee)?; (total <= balance).then_some(Authorization {total_debit: amount})'),
      'forgot_fee': patch('(amount <= balance).then_some(Authorization {total_debit: amount})'),
      'saturating': patch('let total = amount.saturating_add(fee); (total <= balance).then_some(Authorization {total_debit: total})'),
      'rare_trigger': patch('if balance == 9000000000000000000u64 && amount == 1u64 && fee == 2u64 {return None;} let total = amount.checked_add(fee)?; (total <= balance).then_some(Authorization {total_debit: total})'),
    }
    for name, source in variants.items():
        result = verify.check_patch(source)
        expect(result['status']=='pass', (name,result))
    for name, source in rejects.items():
        result = verify.check_patch(source)
        expect(result['status']=='fail', (name,result))
        expect(result['checks']['universal_equivalence']['status']=='fail', (name,result))
        expect(result['checks']['concrete_defense']['status']=='fail', (name,result))
    print(f'Rust: {len(variants)} correct forms accepted; {len(rejects)} incorrect forms rejected universally and concretely')

    unsupported = {
      'loop': patch('loop { }'),
      'signed_literal_rare_trigger': patch('if balance == 9000000000000000000u64 && amount == 1u64 && fee == 2u64 && 1 - 2 < 0 { return None; } let total = amount.checked_add(fee)?; (total <= balance).then_some(Authorization {total_debit: total})'),
      'macro': patch('println!("tamper"); None'),
      'helper': ref + 'fn other() {}',
      'unsafe': patch('unsafe {None}'),
      'attribute': '#![allow(unused)]\n' + ref,
    }
    # Reproduce the interpreter/rustc correspondence regression even though
    # the final backend rejects it before compiled execution in check_patch.
    with tempfile.TemporaryDirectory() as raw:
        tmp=Path(raw); probe=verify.compile_probe(unsupported['signed_literal_rare_trigger'],tmp)
        actual=verify.run([str(probe),'9000000000000000000','1','2'],tmp)
        expect(actual.returncode==0 and actual.stdout.strip()=='none',actual)
    for name, source in unsupported.items():
        try: verify.check_patch(source)
        except spec.Unsupported: pass
        else: raise AssertionError(('unsupported Rust executed', name))


    reference=(TASK/'solution/Spec.lean').read_text()
    def candidate(accept='a.toNat + f.toNat ≤ b.toNat',output='t.toNat = a.toNat + f.toNat',helpers=''):
        return 'import SecurityChallenge\nopen SecurityChallenge\n'+helpers+'\ndef candidateSpec : AuthorizationSpec where\n  accepts := fun b a f => '+accept+'\n  output := fun b a f t => '+output+'\n'
    def check(text):
        return verify.LeanSession(VERIFIER).stage('CandidateSpec',text,'spec')
    for name,text in {
        'reference':reference,
        'commutative':candidate('f.toNat + a.toNat ≤ b.toNat','a.toNat + f.toNat = t.toNat'),
        'guarded_subtraction':candidate('a.toNat ≤ b.toNat ∧ f.toNat ≤ b.toNat - a.toNat'),
        'if':candidate('if a.toNat ≤ b.toNat then f.toNat ≤ b.toNat - a.toNat else False'),
        'helper':candidate('affordable b a f','t.toNat = sum a f',
            'def sum (a f : UInt64) := a.toNat + f.toNat\ndef affordable (b a f : UInt64) := sum a f ≤ b.toNat'),
        'negation':candidate('¬ (b.toNat < a.toNat + f.toNat)'),
        'implication':candidate('(a.toNat + f.toNat ≤ b.toNat) ∧ (True → True)'),
        'let':candidate('(let total := a.toNat + f.toNat; total ≤ b.toNat)'),
        'identity_helper':candidate('a.toNat + f.toNat ≤ (identity b).toNat',helpers='def identity (x : UInt64) := x'),
        'builtin_id':candidate('a.toNat + f.toNat ≤ (id b).toNat'),
    }.items():
        result=check(text); expect(result['status']=='pass',(name,result))
    cases=[
      ('always_true',candidate('True'),'safety','fail'),
      ('always_false',candidate('False'),'completeness','fail'),
      ('weak',candidate('a.toNat ≤ b.toNat'),'safety','fail'),
      ('strict',candidate('a.toNat + f.toNat < b.toNat'),'completeness','fail'),
      ('truncated_subtraction',candidate('f.toNat ≤ b.toNat - a.toNat'),'safety','fail'),
      ('wrong_output',candidate(output='t.toNat = a.toNat'),'output_exactness','fail'),
      ('output_true',candidate(output='True'),'output_exactness','fail'),
      ('output_false',candidate(output='False'),'existence_coherence','fail'),
    ]
    for name,text,facet,status in cases:
        r=check(text); expect(r['facets'][facet]['status']==status,(name,r))
        if name=='output_false':
            expect(r['facets']['output_exactness']['status']=='fail',r)
            expect(r['facets']['output_exactness']['exact_implication']['status']=='pass',r)
            expect('vacuously' in r['vacuity'],r)
    for output in ('False','t.toNat = a.toNat + f.toNat'):
        r=check(candidate('False',output))
        expect(r['credit_fraction']==.25 and r['facets']['existence_coherence']['status']=='fail',r)
    r=check(candidate(output='False')); expect(r['credit_fraction']==.5,r)
    r=check(candidate(output='∀ n : Nat, n = n'))
    expect(r['status']=='partial' and r['facets']['safety']['status']=='pass' and
           r['facets']['output_exactness']['status']=='unsupported',r)
    r=check(candidate('a.toNat * f.toNat ≤ b.toNat'))
    expect(r['status']=='unsupported',r)
    r=check(candidate('(a + f).toNat ≤ b.toNat'))
    expect(r['status']=='unsupported',r)
    for text in ('import SecurityChallenge\ndef candidateSpec : Nat := 0',
                 'import SecurityChallenge\nopen SecurityChallenge\naxiom bad : AuthorizationSpec\ndef candidateSpec := bad',
                 reference.replace('amount.toNat + fee.toNat ≤ balance.toNat','by sorry'),
                 'import Mathlib\n'+reference):
        r=verify.capture(lambda:check(text)); expect(r['status']=='fail',r)
    from unittest.mock import patch as mock
    for status in ('unknown','timeout'):
        with mock('spec.query',return_value={'status':status,'reason':'injected result'}):
            r=check(reference); expect(r['credit_fraction']==0 and r['status']==status,r)
    print('Lean specs: 10 equivalent forms, false/weak/strict/vacuous, truncation, wrong output, unsupported components, type/axiom/import and solver unknown/timeout passed')

    witness=(TASK/'solution/counterexample.json').read_text()
    expect(verify.check_counterexample(witness,VERIFIER)['status']=='pass','reference witness')
    expect(verify.check_counterexample('{"balance":10,"amount":1,"fee":1}',VERIFIER)['status']=='fail','non-witness')
    for bad in ('{"balance":false,"amount":1,"fee":1}','{"balance":0,"amount":18446744073709551616,"fee":1}','{"balance":0,"amount":1,"fee":1,"fee":2}'):
        r=verify.capture(lambda:verify.check_counterexample(bad,VERIFIER)); expect(r['status']=='fail',r)
    print('Witness: pristine actual Rust and malformed/ordinary inputs passed')

    def proof_result(term):
        session=verify.LeanSession(VERIFIER)
        session.stage('CandidateSpec',reference,'spec')
        session.stage('CandidateAudit',(TASK/'solution/Audit.lean').read_text(),'verdict')
        return verify.capture(lambda:session.stage('CandidateProof',term,'proof'))
    proof=(TASK/'solution/Proof.lean').read_text()
    expect(proof_result(proof)['status']=='pass','non-omega proof')
    for term in ('by sorry','by admit','by exact True.intro','by native_decide',
                 'axiom bad : False\nby exact False.elim bad','import Mathlib.Tactic\n'+proof,
                 proof+'\ntheorem escape : True := by trivial'):
        r=proof_result(term); expect(r['status']=='fail',(term,r))
    injected='''by
  run_tac
    Lean.addDecl (.axiomDecl { name := `auditEvidence.fabricated, levelParams := [], type := Lean.mkConst ``False, isUnsafe := false })
  exact False.elim auditEvidence.fabricated
'''
    r=proof_result(injected); expect(r['status']=='fail',r)
    with tempfile.TemporaryDirectory() as raw:
        protected=Path(raw)/'protected.txt'; protected.write_text('pristine')
        malicious='by\n  run_tac\n    Lean.Elab.Tactic.liftMetaTactic fun g => do\n      IO.FS.writeFile '+json.dumps(str(protected))+' "tampered"\n      pure [g]\n'+proof[3:]
        r=proof_result(malicious)
        expect(r['status']=='fail' and protected.read_text()=='pristine',r)
    print('Lean proof: non-omega reference passes; sorry/axiom/import/type/escape/injected axiom and write outside sandbox rejected')

    with tempfile.TemporaryDirectory(prefix='lean-native-family-') as raw:
        raw=Path(raw)
        # A root-run verifier drops untrusted Lean to uid 65534. The generated
        # trusted APIs must remain readable through this temporary parent.
        raw.chmod(0o755)
        family=raw/'family'
        subprocess.run([sys.executable,str(ROOT/'scripts/make-family.py'),str(family),'--build-api'],check=True)

        # Settlement-specific Rust & Lean checks across isolation levels
        settlement_safe_rs=(ROOT/'problems/settlement/safe/lib.rs').read_text()
        settlement_vuln_rs=(ROOT/'problems/settlement/vulnerable/lib.rs').read_text()
        # Rust resolves the imported alias to evil::wrong; the old interpreter
        # instead picked trusted::correct by short name, missing this rare branch.
        alias_patch = settlement_safe_rs.replace('pub fn authorize',
            'pub mod trusted { use crate::Authorization; pub fn correct(b:u64,a:u64,f:u64)->Option<Authorization> { None } }\n'
            'pub mod evil { use crate::Authorization; pub fn wrong(b:u64,a:u64,f:u64)->Option<Authorization> { Some(Authorization { total_debit:0u64 }) } }\n'
            'use crate::evil::wrong as correct;\npub fn authorize').replace(
            '    let raw_sum',
            '    if balance == 0u64 && amount == 9000000000000000000u64 && fee == 0u64 { return correct(balance,amount,fee); }\n    let raw_sum', 1)
        duplicate_patch = alias_patch.replace('wrong', 'correct').replace(' as correct', '')
        for name, source in (('renamed_import', alias_patch), ('duplicate_item', duplicate_patch)):
            with tempfile.TemporaryDirectory() as raw:
                tmp = Path(raw); probe = verify.compile_probe(source, tmp)
                actual = verify.run([str(probe), '0', '9000000000000000000', '0'], tmp)
                expect(actual.returncode == 0 and actual.stdout.strip() == 'some:0', (name, actual))
            try: verify.check_patch(source, problem='settlement')
            except spec.Unsupported: pass
            else: raise AssertionError((name, 'ambiguous Rust name resolution accepted'))
        for untrusted in ('use std::process::exit;\n', 'use ::std::process::exit;\n'):
            try: rust_symbolic.check(untrusted + settlement_safe_rs, problem='settlement')
            except spec.Unsupported: pass
            else: raise AssertionError('external import accepted')
        settlement_div_ceil_rs=settlement_safe_rs.replace(
            '(((raw_sum % BPS_DENOM) + BPS_MAX_REM) / BPS_DENOM)',
            '(raw_sum % BPS_DENOM).div_ceil(BPS_DENOM)')
        settlement_naive_checked_rs=settlement_safe_rs.replace(
            'let raw_sum = amount.wrapping_add(fee);\n    let gross_fee = if raw_sum < amount {\n        let folded_rem = (raw_sum % BPS_DENOM) + U64_MOD_BPS_REM;\n        U64_MOD_BPS_QUOT + (raw_sum / BPS_DENOM) + ((folded_rem + BPS_MAX_REM) / BPS_DENOM)\n    } else {',
            'let raw_sum = amount.checked_add(fee)?;\n    let gross_fee = {')
        settlement_u128_rs=settlement_safe_rs.replace(
            'let raw_sum = amount.wrapping_add(fee);',
            'let _wide: u128 = amount as u128;\n    let raw_sum = amount.wrapping_add(fee);')
        for sname,ssrc in (('settlement_safe',settlement_safe_rs),('settlement_div_ceil',settlement_div_ceil_rs)):
            r=verify.check_patch(ssrc,problem='settlement')
            expect(r['status']=='pass',(sname,r))
        for sname,ssrc in (('settlement_vuln',settlement_vuln_rs),('settlement_naive_checked',settlement_naive_checked_rs)):
            r=verify.check_patch(ssrc,problem='settlement')
            expect(r['status']=='fail' and r['checks']['universal_equivalence']['status']=='fail' and r['checks']['concrete_defense']['status']=='fail',(sname,r))
        try: verify.check_patch(settlement_u128_rs,problem='settlement')
        except spec.Unsupported: pass
        else: raise AssertionError('u128 cast allowed in settlement')
        for bad_div in (candidate('a.toNat / f.toNat ≤ b.toNat'),candidate('a.toNat % f.toNat ≤ b.toNat'),candidate('a.toNat / 0 ≤ b.toNat')):
            expect(check(bad_div)['status']=='unsupported',bad_div)

        instructions=[]
        for problem in ('authorization','settlement','settlement-modular','settlement-engine'):
            for variant in ('vulnerable','safe'):
                task_name=problem+'-'+variant
                task=family/task_name
                instructions.append((task/'instruction.md').read_bytes())
                verifier=task/'tests/verifier'
                workspace=task/'environment/workspace'
                subprocess.run(['cargo','test','--release','--quiet'],cwd=workspace/'challenge',check=True)
                skeleton=verify.grade(workspace,verifier)
                expect(skeleton['reward']==0,(task_name,'skeleton',skeleton))
                for rel in ('Spec.lean','Audit.lean','Proof.lean','counterexample.json','src/lib.rs'):
                    if (task/'solution'/rel).is_file():
                        (workspace/'submission'/rel).parent.mkdir(parents=True,exist_ok=True)
                        shutil.copy(task/'solution'/rel,workspace/'submission'/rel)
                reference_result=verify.grade(workspace,verifier)
                expect(reference_result['reward']==1,(task_name,reference_result))
                if os.environ.get('V3_EVIDENCE_DIR'):
                    dest=Path(os.environ['V3_EVIDENCE_DIR']); dest.mkdir(parents=True,exist_ok=True)
                    fname=(variant+'-reference.json') if problem=='authorization' else (task_name+'-reference.json')
                    (dest/fname).write_text(json.dumps(reference_result,indent=2)+'\n')
                if variant=='safe':
                    (workspace/'submission/Proof.lean').write_text('by exact True.intro')
                    r=verify.grade(workspace,verifier)
                    expect(r['checkpoints']['verdict']['score']==0 and r['checkpoints']['response']['score']==0,r)
                    shutil.copy(task/'solution/Proof.lean',workspace/'submission/Proof.lean')
                    (workspace/'submission/counterexample.json').write_text(witness)
                    r=verify.grade(workspace,verifier)
                    expect(r['checkpoints']['response']['score']==0,r)
                    for rel in ('counterexample.json','src/lib.rs'):
                        extra=workspace/'submission'/rel
                        extra.parent.mkdir(parents=True,exist_ok=True)
                        for payload in (b'\xff',b'x'*65537):
                            extra.write_bytes(payload)
                            expect(rel in verify.unexpected_safe_artifacts(workspace/'submission'),rel)
                        extra.unlink(); extra.symlink_to('/nonexistent-untrusted-target')
                        expect(rel in verify.unexpected_safe_artifacts(workspace/'submission'),rel)
                        extra.unlink()
                    optional=workspace/'submission/counterexample.json'
                    for payload in (b'\xff',b'x'*65537):
                        optional.write_bytes(payload)
                        r=verify.grade(workspace,verifier)
                        expect(r['checkpoints']['response']['score']==0 and r['status']=='ok',r)
                    optional.unlink(); optional.symlink_to('/nonexistent-untrusted-target')
                    r=verify.grade(workspace,verifier)
                    expect(r['checkpoints']['response']['score']==0 and r['status']=='ok',r)
                else:
                    if problem.startswith('settlement'):
                        # Off-by-one balance in the carry pocket must fail witness verification
                        expect(verify.check_counterexample('{"balance":1660206966633860,"amount":0,"fee":18446744073709541617}',verifier,problem=problem)['status']=='fail',task_name+' off-by-one witness')
                    (workspace/'submission/Spec.lean').write_text('NOT LEAN')
                    (workspace/'challenge/src/lib.rs').write_text('NOT RUST')
                    r=verify.grade(workspace,verifier)
                    expect(r['checkpoints']['verdict']['score']==.15 and r['checkpoints']['response']['score']==.35,r)
                    expect(r['checkpoints']['response']['checks']['counterexample']['status']=='pass',r)
                    symlink=workspace/'submission/counterexample.json'; symlink.unlink(); symlink.symlink_to(task/'solution/counterexample.json')
                    r=verify.grade(workspace,verifier); expect(r['checkpoints']['response']['checks']['counterexample']['status']=='fail',r)
                print(task_name+': reference=1.00 skeleton=0.00; verdict/evidence and independent response checked')
        expect(len(set(instructions))==1,'prompts differ')
    print('selftest v3: PASS')

if __name__=='__main__':main()

