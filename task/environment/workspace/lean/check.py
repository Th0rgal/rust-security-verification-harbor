#!/usr/bin/env python3
"""Local Lean compilation check; isolated grading remains authoritative."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
submission = root.parent / 'submission'

LEAN_MODEL_ORDER = (
    'Constants',
    'WordMath',
    'ReciprocalDiv',
    'BroadwordSwar',
    'MontgomeryField',
    'GoldilocksField',
    'FeeSchedule',
    'LiquidityPool',
    'TranscriptCodec',
    'ClearingPipeline',
)


def _extra_lean_paths():
    paths = []
    deps_root = Path('/opt/rvb-deps')
    if deps_root.is_dir():
        top_lib = deps_root / '.lake/build/lib/lean'
        if top_lib.is_dir():
            paths.append(str(top_lib))
        pkgs = deps_root / 'packages'
        if pkgs.is_dir():
            for pkg_lib in sorted(pkgs.glob('*/.lake/build/lib/lean')):
                if pkg_lib.is_dir():
                    paths.append(str(pkg_lib))
    return paths


def _split_imports(text):
    text = re.sub(r'--[^\n]*', '', text)
    while '/-' in text:
        start = text.index('/-')
        pos = start + 2
        depth = 1
        while depth and pos < len(text):
            if text.startswith('/-', pos):
                depth += 1
                pos += 2
            elif text.startswith('-/', pos):
                depth -= 1
                pos += 2
            else:
                pos += 1
        if depth:
            raise ValueError('unterminated Lean comment')
        text = text[:start] + ' ' + text[pos:]
    extra_imports = []
    for line in text.splitlines():
        if line.strip().startswith('import '):
            for m in line.split()[1:]:
                if m != 'SecurityChallenge' and m not in extra_imports:
                    extra_imports.append(m)
    remaining = re.sub(r'^\s*import [^\n]*', '', text, flags=re.M)
    import_block = ''.join(f'import {m}\n' for m in extra_imports)
    return import_block, remaining


with tempfile.TemporaryDirectory(prefix='local-lean-') as raw:
    tmp = Path(raw)
    lean_paths = [str(tmp), str(root)] + _extra_lean_paths()
    env = {**os.environ, 'LEAN_PATH': ':'.join(lean_paths)}
    sub_lean = submission / 'LeanModel'
    root_lean = root / 'LeanModel'
    if sub_lean.is_dir() and root_lean.is_dir():
        (tmp / 'LeanModel').mkdir(parents=True, exist_ok=True)
        protected_mods = ('Constants', 'FeeSchedule', 'LiquidityPool', 'TranscriptCodec', 'ClearingPipeline')
        direct_changes = 0
        changed_mods = set()
        for m in LEAN_MODEL_ORDER:
            rel = f'LeanModel/{m}.lean'
            rel_olean = f'LeanModel/{m}.olean'
            orig_file = root_lean / f'{m}.lean'
            orig_olean = root / rel_olean
            sub_file = sub_lean / f'{m}.lean'
            if not orig_file.is_file():
                continue
            orig_text = orig_file.read_text()
            src_text = sub_file.read_text() if sub_file.is_file() else orig_text
            if src_text.strip() != orig_text.strip():
                if m in protected_mods:
                    raise SystemExit(f'{rel} is a protected protocol orchestration module; patch the defective low-level arithmetic module instead')
                direct_changes += 1
                if direct_changes > 1:
                    raise SystemExit('submission/LeanModel patch must modify only the single defective arithmetic module')
            deps = set(re.findall(r'import\s+LeanModel\.([A-Za-z0-9_]+)', src_text))
            if src_text.strip() != orig_text.strip() or (deps & changed_mods) or not orig_olean.is_file():
                changed_mods.add(m)
                (tmp / rel).write_text(src_text)
                subprocess.run(['lean', '-j1', '-M4096', '-o', rel_olean, rel], cwd=tmp, env=env, check=True)
            else:
                shutil.copy(orig_olean, tmp / rel_olean)
        if changed_mods and (root / 'SecurityChallenge.lean').is_file():
            shutil.copy(root / 'SecurityChallenge.lean', tmp / 'SecurityChallenge.lean')
            subprocess.run(['lean', '-j1', '-M4096', '-o', 'SecurityChallenge.olean', 'SecurityChallenge.lean'], cwd=tmp, env=env, check=True)
    for name, rel in [('CandidateSpec', 'Spec.lean'), ('CandidateAudit', 'Audit.lean')]:
        imp, body = _split_imports((submission / rel).read_text())
        (tmp / (name + '.lean')).write_text('import SecurityChallenge\n' + imp + body + '\n')
        subprocess.run(['lean', '-j1', '-M4096', '-o', name + '.olean', name + '.lean'], cwd=tmp, env=env, check=True)
    imp, body = _split_imports((submission / 'Proof.lean').read_text())
    proof = (
        'import SecurityChallenge\nimport CandidateSpec\nimport CandidateAudit\nimport Lean\nimport Std\n'
        + imp
        + 'open SecurityChallenge\ntheorem auditEvidence : AuditClaim candidateSpec verdict := (\n'
        + body
        + '\n)\n'
    )
    (tmp / 'CandidateProof.lean').write_text(proof)
    raise SystemExit(subprocess.call(['lean', '-j1', '-M4096', 'CandidateProof.lean'], cwd=tmp, env=env))
