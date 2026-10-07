#!/usr/bin/env python3
"""Generate symmetric Harbor task pairs from the shared source kernel."""
import argparse
from pathlib import Path
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
PROBLEMS=('authorization','settlement','settlement-modular','settlement-engine','goldilocks','whirlpool','plonky3')
p=argparse.ArgumentParser()
p.add_argument('output',type=Path)
p.add_argument('--problem',choices=('all',)+PROBLEMS,default='all',help='which task family to generate')
p.add_argument('--build-api',action='store_true',help='rebuild pinned Lean APIs with local lake')
a=p.parse_args()
selected=PROBLEMS if a.problem=='all' else (a.problem,)
for problem in selected:
    for variant in ('vulnerable','safe'):
        task=a.output/(problem+'-'+variant)
        if task.exists(): raise SystemExit('refusing to overwrite '+str(task))
        shutil.copytree(ROOT/'task',task,ignore=shutil.ignore_patterns('.lake','__pycache__','target','LocalProof.lean'))
        manifest=task/'task.toml'
        manifest.write_text(manifest.read_text().replace('lfglabs/rust-security-overflow-prove-or-refute','lfglabs/'+problem+'-'+variant))
        verifier=task/'tests/verifier'
        (verifier/'variant.txt').write_text(variant+'\n')
        (verifier/'problem.txt').write_text(problem+'\n')
        if problem=='authorization':
            if variant=='safe':
                for path in (task/'environment/workspace/challenge/src/lib.rs',verifier/'pristine/lib.rs'):
                    text=path.read_text().replace('let total = amount.wrapping_add(fee);','let total = amount.checked_add(fee)?;')
                    path.write_text(text)
                model=verifier/'SecurityChallenge.lean'
                model.write_text(model.read_text().replace(
                    'let total := amount + fee\n  if total.toNat ≤ balance.toNat then some total else none',
                    'let total := amount.toNat + fee.toNat\n  if total < 2^64 ∧ total ≤ balance.toNat then some (UInt64.ofNat total) else none'))
                (task/'solution/Audit.lean').write_text('import SecurityChallenge\nopen SecurityChallenge\ndef verdict : AuditVerdict := .safe\n')
                shutil.copy(ROOT/'scripts/references/safe-Proof.lean',task/'solution/Proof.lean')
                (task/'solution/counterexample.json').unlink()
                (task/'solution/src/lib.rs').unlink()
        else:
            pdir=ROOT/'problems'/problem
            for path in (task/'environment/workspace/challenge/src/lib.rs',verifier/'pristine/lib.rs'):
                shutil.copy(pdir/variant/'lib.rs',path)
            shutil.copy(pdir/variant/'SecurityChallenge.lean',verifier/'SecurityChallenge.lean')
            shutil.copy(pdir/'solution/Spec.lean',task/'solution/Spec.lean')
            shutil.copy(pdir/'solution'/variant/'Audit.lean',task/'solution/Audit.lean')
            shutil.copy(pdir/'solution'/variant/'Proof.lean',task/'solution/Proof.lean')
            if variant=='vulnerable':
                shutil.copy(pdir/'solution/vulnerable/counterexample.json',task/'solution/counterexample.json')
                shutil.copy(pdir/'solution/vulnerable/src/lib.rs',task/'solution/src/lib.rs')
            else:
                (task/'solution/counterexample.json').unlink()
                (task/'solution/src/lib.rs').unlink()
        shutil.copy(verifier/'SecurityChallenge.lean',task/'environment/workspace/lean/SecurityChallenge.lean')
        # The agent Dockerfile also recompiles this visible source. Never rely on
        # the copied vulnerable .olean when generating the safe task.
        if a.build_api:
            subprocess.run(['lake','build','SecurityChallenge','SpecAudit'],cwd=verifier,check=True)
            shutil.copy(verifier/'.lake/build/lib/lean/SecurityChallenge.olean',task/'environment/workspace/lean/SecurityChallenge.olean')
    assert (a.output/(problem+'-safe/instruction.md')).read_bytes()==(a.output/(problem+'-vulnerable/instruction.md')).read_bytes()
print(a.output)

