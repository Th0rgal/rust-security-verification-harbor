#!/usr/bin/env python3
"""Generate symmetric Harbor task pairs from the shared source kernel.

By default (`--problem challenge`), generates the flagship multi-module
`zk-clearing` Challenge Benchmark pair (`zk-clearing-vulnerable` and
`zk-clearing-safe`). Pass `--problem all` to also generate the single-file
calibration/regression pairs.
"""
import argparse
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE_PROBLEMS = ('zk-clearing',)
ALL_PROBLEMS = (
    'authorization',
    'settlement',
    'settlement-modular',
    'settlement-engine',
    'goldilocks',
    'whirlpool',
    'plonky3',
    'succinct',
    'openpql',
    'ruint',
    'zk-clearing',
)

p = argparse.ArgumentParser()
p.add_argument('output', type=Path)
p.add_argument(
    '--problem',
    choices=('challenge', 'all') + ALL_PROBLEMS,
    default='challenge',
    help='which task family to generate (default: challenge = zk-clearing flagship pair)',
)
p.add_argument('--build-api', action='store_true', help='rebuild pinned Lean APIs with local lake')
a = p.parse_args()
selected = CHALLENGE_PROBLEMS if a.problem == 'challenge' else (ALL_PROBLEMS if a.problem == 'all' else (a.problem,))

for problem in selected:
    for variant in ('vulnerable', 'safe'):
        task = a.output / (problem + '-' + variant)
        if task.exists():
            raise SystemExit('refusing to overwrite ' + str(task))
        shutil.copytree(
            ROOT / 'task',
            task,
            ignore=shutil.ignore_patterns('.lake', '__pycache__', 'target', 'LocalProof.lean', '*.olean', '*.ilean', '*.olean.*'),
        )
        manifest = task / 'task.toml'
        manifest.write_text(
            manifest.read_text().replace('lfglabs/rust-security-overflow-prove-or-refute', 'lfglabs/' + problem + '-' + variant)
        )
        verifier = task / 'tests/verifier'
        (verifier / 'variant.txt').write_text(variant + '\n')
        (verifier / 'problem.txt').write_text(problem + '\n')

        if problem == 'authorization':
            if variant == 'safe':
                for path in (task / 'environment/workspace/challenge/src/lib.rs', verifier / 'pristine/lib.rs'):
                    path.write_text(path.read_text().replace('let total = amount.wrapping_add(fee);', 'let total = amount.checked_add(fee)?;'))
                sc = verifier / 'SecurityChallenge.lean'
                sc.write_text(sc.read_text().replace(
                    'let total := amount + fee\n  if total.toNat ≤ balance.toNat then some total else none',
                    'let total := amount.toNat + fee.toNat\n  if total < 2^64 ∧ total ≤ balance.toNat then some (UInt64.ofNat total) else none',
                ))
                (task / 'solution/Audit.lean').write_text('import SecurityChallenge\nopen SecurityChallenge\ndef verdict : AuditVerdict := .safe\n')
                shutil.copy(ROOT / 'scripts/references/safe-Proof.lean', task / 'solution/Proof.lean')
                (task / 'solution/counterexample.json').unlink()
                (task / 'solution/src/lib.rs').unlink()
        else:
            for clean_dir in (
                task / 'environment/workspace/challenge/src',
                task / 'environment/workspace/lean/LeanModel',
                verifier / 'pristine/src',
                verifier / 'pristine/LeanModel',
                verifier / 'LeanModel',
                task / 'solution/src',
                task / 'solution/LeanModel',
            ):
                if clean_dir.is_dir():
                    shutil.rmtree(clean_dir)
            for clean_file in (
                verifier / 'pristine/lib.rs',
                verifier / 'pristine/SecurityChallenge.lean',
                task / 'solution/counterexample.json',
            ):
                if clean_file.is_file():
                    clean_file.unlink()

            pdir = ROOT / 'problems' / problem
            if (pdir / variant / 'src').is_dir():
                shutil.copytree(pdir / variant / 'src', task / 'environment/workspace/challenge/src')
                shutil.copytree(pdir / variant / 'src', verifier / 'pristine/src')
                shutil.copy(pdir / variant / 'src/lib.rs', verifier / 'pristine/lib.rs')
            else:
                (task / 'environment/workspace/challenge/src').mkdir(parents=True, exist_ok=True)
                (verifier / 'pristine').mkdir(parents=True, exist_ok=True)
                for path in (task / 'environment/workspace/challenge/src/lib.rs', verifier / 'pristine/lib.rs'):
                    shutil.copy(pdir / variant / 'lib.rs', path)

            if (pdir / variant / 'LeanModel').is_dir():
                shutil.copytree(pdir / variant / 'LeanModel', verifier / 'LeanModel')
                shutil.copytree(pdir / variant / 'LeanModel', verifier / 'pristine/LeanModel')
                shutil.copytree(pdir / variant / 'LeanModel', task / 'environment/workspace/lean/LeanModel')

            shutil.copy(pdir / variant / 'SecurityChallenge.lean', verifier / 'SecurityChallenge.lean')
            shutil.copy(pdir / variant / 'SecurityChallenge.lean', verifier / 'pristine/SecurityChallenge.lean')
            shutil.copy(pdir / 'solution/Spec.lean', task / 'solution/Spec.lean')
            shutil.copy(pdir / 'solution' / variant / 'Audit.lean', task / 'solution/Audit.lean')
            shutil.copy(pdir / 'solution' / variant / 'Proof.lean', task / 'solution/Proof.lean')
            if variant == 'vulnerable':
                shutil.copy(pdir / 'solution/vulnerable/counterexample.json', task / 'solution/counterexample.json')
                if (pdir / 'solution/vulnerable/src').is_dir():
                    shutil.copytree(pdir / 'solution/vulnerable/src', task / 'solution/src')
                if (pdir / 'solution/vulnerable/LeanModel').is_dir():
                    shutil.copytree(pdir / 'solution/vulnerable/LeanModel', task / 'solution/LeanModel')

        shutil.copy(verifier / 'SecurityChallenge.lean', task / 'environment/workspace/lean/SecurityChallenge.lean')
        if a.build_api:
            subprocess.run(['lake', 'build', 'SecurityChallenge', 'SpecAudit'], cwd=verifier, check=True)
            shutil.copy(
                verifier / '.lake/build/lib/lean/SecurityChallenge.olean',
                task / 'environment/workspace/lean/SecurityChallenge.olean',
            )
            built_lm = verifier / '.lake/build/lib/lean/LeanModel'
            if built_lm.is_dir():
                target_lm = task / 'environment/workspace/lean/LeanModel'
                target_lm.mkdir(parents=True, exist_ok=True)
                for olean in built_lm.glob('*.olean'):
                    shutil.copy(olean, target_lm / olean.name)
    assert (a.output / (problem + '-safe/instruction.md')).read_bytes() == (
        a.output / (problem + '-vulnerable/instruction.md')
    ).read_bytes()
print(a.output)
