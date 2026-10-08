#!/usr/bin/env python3
"""Local Lean compilation check; isolated grading remains authoritative."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parent
submission = root.parent / 'submission'


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
    lean_paths = [str(root), str(tmp)] + _extra_lean_paths()
    env = {**os.environ, 'LEAN_PATH': ':'.join(lean_paths)}
    for name, rel in [('CandidateSpec', 'Spec.lean'), ('CandidateAudit', 'Audit.lean')]:
        imp, body = _split_imports((submission / rel).read_text())
        (tmp / (name + '.lean')).write_text('import SecurityChallenge\n' + imp + body + '\n')
        subprocess.run(['lean', '-o', name + '.olean', name + '.lean'], cwd=tmp, env=env, check=True)
    imp, body = _split_imports((submission / 'Proof.lean').read_text())
    proof = (
        'import SecurityChallenge\nimport CandidateSpec\nimport CandidateAudit\nimport Lean\nimport Std\n'
        + imp
        + 'open SecurityChallenge\ntheorem auditEvidence : AuditClaim candidateSpec verdict := (\n'
        + body
        + '\n)\n'
    )
    (tmp / 'CandidateProof.lean').write_text(proof)
    raise SystemExit(subprocess.call(['lean', 'CandidateProof.lean'], cwd=tmp, env=env))
