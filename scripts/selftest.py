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

    typed = json.loads((TASK/'solution/spec.json').read_text())
    expect(spec.check(typed)['status']=='pass','typed reference')
    for prop in ('amount + fee <= balance','authorized_total_le_balance'):
        legacy=spec.check({'property':prop,'arithmetic':'mathematical_unsigned','on_overflow':'reject'})
        expect(legacy['status']=='partial' and legacy['credit_fraction']==.5,legacy)
        expect(legacy['facets']['total_debit']['status']=='missing',legacy)
        expect(legacy['facets']['completeness']['status']=='missing',legacy)
    def check_expr(expression): return spec.check({'version':2,'accept':expression})
    add = {'op':'add','args':['amount','fee']}
    cases = [('true',True,'pass','fail'),('false',False,'fail','pass'),
      ('weak',{'op':'le','args':['amount','balance']},'pass','fail'),
      ('strong',{'op':'lt','args':[add,'balance']},'fail','pass')]
    for name, expr, validity, safety in cases:
        result = check_expr(expr); c = result['checks']
        expect(result['status']!='pass',(name,result))
        expect(c['reference_validity']['status']==validity,(name,result))
        expect(c['safety_adequacy']['status']==safety,(name,result))
    expect(check_expr({'op':'add','args':[True,1]})['status']=='fail','type error')
    deep = True
    for _ in range(15): deep={'op':'not','args':[deep]}
    expect(check_expr(deep)['status']=='fail','depth bound')
    try: verify.json_object('{"version":2,"version":2}')
    except ValueError: pass
    else: raise AssertionError('duplicate JSON keys')
    # Each contract facet must stand on its own; mathematical add does not
    # silently specify Some.total_debit, explicit overflow or an iff contract.
    bare=spec.check({'version':2,'accept':typed['accept']})
    expect(bare['credit_fraction']==.25 and bare['status']=='partial',bare)
    for field in ('total_debit','on_overflow','completeness'):
        reduced={k:v for k,v in typed.items() if k!=field}
        result=spec.check(reduced)
        expect(result['credit_fraction']==.75,(field,result))
    wrong=dict(typed,total_debit='amount'); result=spec.check(wrong)
    expect(result['facets']['total_debit']['status']=='fail',result)
    weak=dict(typed,accept={'op':'le','args':['amount','balance']}); result=spec.check(weak)
    expect(result['facets']['explicit_overflow']['status']=='fail',result)
    strict=dict(typed,accept={'op':'lt','args':[add,'balance']}); result=spec.check(strict)
    expect(result['facets']['completeness']['status']=='fail',result)
    vacuous=dict(typed,accept=False); result=spec.check(vacuous)
    expect(result['credit_fraction']==0,result)
    swapped=dict(typed,total_debit={'op':'add','args':['fee','amount']})
    expect(spec.check(swapped)['status']=='pass','commutative output')
    malformed=[dict(typed,total_debit=True),dict(typed,version=True),dict(typed,on_overflow='wrap'),
               dict(typed,completeness=True),dict(typed,extra=1),
               {'version':2,'accept':{'op':'le','args':[-1,'balance']}},
               {'version':2,'accept':{'op':'le','args':[2**128,'balance']}},
               {'version':2,'accept':{'op':'mul','args':['amount','fee']}}]
    for obj in malformed: expect(spec.check(obj)['credit_fraction']==0,obj)
    wide=True
    for _ in range(6): wide={'op':'and','args':[wide,wide]}
    expect(check_expr(wide)['credit_fraction']==0,'node bound')
    # Timeout/unknown is never upgraded to successful universal evidence.
    from unittest.mock import patch as mock
    for status in ('unknown','timeout'):
        with mock('spec.query',return_value={'status':status,'reason':'injected solver result'}):
            result=spec.check(typed)
            expect(result['status']==status and result['credit_fraction']==0,result)
    combined=True
    for _ in range(5): combined={'op':'and','args':[combined,combined]}
    too_many=dict(typed,accept=combined)
    expect(spec.check(too_many)['credit_fraction']==0,'combined expression node bound')
    print('Spec: all four facets, weak/strict/vacuous/wrong output, legacy partial, typing/bounds and unknown/timeout passed')

    witness=(TASK/'solution/counterexample.json').read_text()
    expect(verify.check_counterexample(witness,VERIFIER)['status']=='pass','reference witness')
    expect(verify.check_counterexample('{"balance":10,"amount":1,"fee":1}',VERIFIER)['status']=='fail','non-exploit witness')
    for obj in ({'balance':False,'amount':2**64-1,'fee':1},
                {'balance':0,'amount':2**64,'fee':1},
                {'balance':0,'amount':2**64-1,'fee':1.0},
                {'balance':0,'amount':2**64-1,'fee':1,'extra':0}):
        try: verify.check_counterexample(json.dumps(obj),VERIFIER)
        except ValueError: pass
        else: raise AssertionError(('malformed witness accepted',obj))
    print('Witness: pristine exploit, non-exploit and malformed u64/JSON cases passed')

    proof = (TASK/'solution/Proof.lean').read_text()
    for term in (proof, 'import Lean\n'+proof,
                 'by\n  have facts := (repairedAuthorize_success balance amount fee total).mp h\n  constructor\n  · exact facts.1.symm\n  · omega'):
        result=verify.check_proof(term, VERIFIER)
        expect(result['status']=='pass',result)
    bad_proofs = ['by sorry', 'by admit', 'axiom bad : False\nby exact False.elim bad',
                  'import Mathlib.Tactic\n'+proof, 'by native_decide', 'by exact True.intro', proof+'\ntheorem escape : True := by trivial', 'by\n  exact False.elim (by sorry)']
    for term in bad_proofs:
        try: result=verify.check_proof(term, VERIFIER)
        except ValueError: continue
        expect(result['status']=='fail',result)
    injected = '''by
  run_tac
    Lean.addDecl (.axiomDecl { name := `patched_authorize_sound.fabricated, levelParams := [], type := Lean.mkConst ``False, isUnsafe := false })
  exact False.elim patched_authorize_sound.fabricated
'''
    result=verify.check_proof(injected, VERIFIER)
    expect(result['status']=='fail',result)
    expect('axiom' in result.get('diagnostic',''),result)
    with tempfile.TemporaryDirectory() as raw:
        protected=Path(raw)/'protected.txt'; protected.write_text('pristine')
        malicious='by\n  run_tac\n    Lean.Elab.Tactic.liftMetaTactic fun g => do\n      IO.FS.writeFile '+json.dumps(str(protected))+' "tampered"\n      pure [g]\n'+proof[3:]
        result=verify.check_proof(malicious,VERIFIER)
        expect(result['status']=='fail',result)
        expect(protected.read_text()=='pristine','proof sandbox file isolation')
        expect(any(x in result.get('diagnostic','').lower() for x in ('permission denied','not permitted')),result)
    print('Lean: 3 valid proofs accepted; sorry/axiom/import/unsafe execution and injected axiom rejected')

    with tempfile.TemporaryDirectory(prefix='semantic-selftest-') as raw:
        root=Path(raw); workspace=root/'workspace'
        shutil.copytree(TASK/'environment/workspace',workspace)
        details=verify.grade(workspace,VERIFIER)
        expect(details['reward']==0,details)
        for rel in ('spec.json','counterexample.json','src/lib.rs','Proof.lean'):
            shutil.copy(TASK/'solution'/rel,workspace/'submission'/rel)
        details=verify.grade(workspace,VERIFIER)
        expect(details['reward']==1.0,details)
        # No previous checkpoint gates: witness, patch and proof earn .80 alone.
        (workspace/'submission/spec.json').write_text('{}')
        details=verify.grade(workspace,VERIFIER)
        expect(details['reward']==.8,details)
        expect(details['checkpoints']['spec']['status']=='missing',details)
        # Editing the visible challenge has no effect on witness execution.
        (workspace/'challenge/src/lib.rs').write_text('THIS IS NOT RUST')
        details=verify.grade(workspace,VERIFIER)
        expect(details['checkpoints']['counterexample']['status']=='pass',details)
        witness=workspace/'submission/counterexample.json'; witness.unlink()
        witness.symlink_to(TASK/'solution/counterexample.json')
        details=verify.grade(workspace,VERIFIER)
        expect(details['checkpoints']['counterexample']['status']=='fail',details)
        expect(details['checkpoints']['patch']['status']=='pass',details)
        # Oversized artifacts and links in nested source parents fail closed.
        specfile=workspace/'submission/spec.json'
        specfile.write_text(' '*65537)
        expect(verify.grade(workspace,VERIFIER)['checkpoints']['spec']['status']=='fail','artifact size bound')
        srcdir=workspace/'submission/src'; shutil.rmtree(srcdir)
        srcdir.symlink_to(TASK/'solution/src',target_is_directory=True)
        details=verify.grade(workspace,VERIFIER)
        expect(details['checkpoints']['patch']['status']=='fail','source parent symlink')
        srcdir.unlink(); srcdir.mkdir()
        # Explicit READY contains no textual checked_add requirement.
        witness.unlink(); shutil.copy(TASK/'solution/counterexample.json',witness)
        shutil.copy(TASK/'solution/spec.json',workspace/'submission/spec.json')
        (workspace/'submission/src/lib.rs').write_text(variants['wide'])
        ready=subprocess.run([sys.executable,str(TASK/'environment/workspace/harness/checkpoint.py'),
                              '--workspace',str(workspace)],text=True,capture_output=True)
        expect('\nREADY\n' in ready.stdout,ready.stdout)
        # Exact real snapshot replay; artifacts are immutable fixtures with original hashes.
        fixture=ROOT/'scripts/fixtures/glm-5.3-flash'
        for line in (fixture/'original-SHA256SUMS').read_text().splitlines():
            digest, rel=line.split(None,1)
            rel = 'submission/' + rel.split('/submission/', 1)[-1]
            if rel.startswith('submission/'):
                expect(hashlib.sha256((fixture/rel).read_bytes()).hexdigest()==digest,'GLM fixture drift: '+rel)
        glm=verify.grade(fixture,VERIFIER)
        expect(glm['reward']==.6,glm)
        expect([x['status'] for x in glm['checkpoints'].values()]==['partial','pass','pass','fail'],glm)
        # Write replay evidence outside source tree unless explicitly requested.
        if os.environ.get('GLM_DETAILS_OUT'):
            Path(os.environ['GLM_DETAILS_OUT']).write_text(json.dumps(glm,indent=2)+'\n')
        print('GLM actual snapshot: spec=.10 (safety=.05, overflow=.05; output/completeness missing) witness=.25 patch=.25 proof=.00 total=.60')
        print('Reference=1.00; skeleton=0.00; missing spec with independent credits=.80; pristine/READY checks passed')
    with tempfile.TemporaryDirectory(prefix='semantic-family-') as raw:
        out=Path(raw)/'family'
        subprocess.run([sys.executable,str(ROOT/'scripts/make-family.py'),str(out)],check=True,capture_output=True)
        for profile in ('specify','refute'):
            task=out/('overflow-'+profile)
            expect(not (task/'environment/workspace/lean').exists(),'discovery exposes Lean contract')
            public=(task/'instruction.md').read_text()+(task/'environment/workspace/spec.schema.json').read_text()
            for leaked in ('amount + fee <= balance','repairedAuthorize_success','checked_add','authorized_total_le_balance'):
                expect(leaked not in public,('discovery leak',profile,leaked))
            expect('Signature.lean' not in (task/'environment/Dockerfile').read_text(),'broken discovery Dockerfile')
    print('Discovery: isolated prompts/schema/images omit the repaired Lean contract and solution examples')
    print('selftest: PASS')

if __name__=='__main__':main()
