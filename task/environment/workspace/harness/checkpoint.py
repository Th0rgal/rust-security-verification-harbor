#!/usr/bin/env python3
"""Readiness hints only: independent artifacts, explicit READY, no textual patch gate."""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--workspace', type=Path, default=Path('/workspace'))
p.add_argument('--profile', choices=['integrated','specify','refute','repair','prove'], default='integrated')
a = p.parse_args(); root = a.workspace/'submission'
artifacts = {'specify':'spec.json', 'refute':'counterexample.json', 'repair':'src/lib.rs', 'prove':'Proof.lean'}
hints = {'specify':'Specify a mathematical acceptance predicate using the bounded typed DSL.',
         'refute':'Find a pristine release-Rust authorization whose mathematical total exceeds balance.',
         'repair':'Preserve the API and return Some exactly when the mathematical total is affordable.',
         'prove':'Use lean/Signature.lean and the opaque API; run python3 /workspace/lean/check.py.'}
ready = True
for stage, rel in artifacts.items():
    if a.profile not in ('integrated', stage): continue
    try:
        source = (root/rel).read_text().strip()
        populated = bool(source)
        if rel.endswith('.json'): populated = bool(json.loads(source))
        if stage == 'prove': populated = populated and 'sorry' not in source
        if stage == 'repair': populated = populated and 'todo!' not in source
    except (OSError, ValueError): populated = False
    print(f'{stage.upper()}: ' + ('POPULATED' if populated else 'MISSING — '+hints[stage]))
    ready &= populated
print('READY' if ready else 'NOT_READY')
print('Readiness is advisory. All checkpoints receive independent semantic verdicts.')
