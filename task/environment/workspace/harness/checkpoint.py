#!/usr/bin/env python3
"""Show submitted files; this convenience helper does not grade semantics."""
from pathlib import Path
import argparse
p=argparse.ArgumentParser(); p.add_argument('--workspace',type=Path,default=Path('/workspace')); a=p.parse_args()
for rel in ('Spec.lean','Audit.lean','Proof.lean','counterexample.json','src/lib.rs'):
    path=a.workspace/'submission'/rel
    print(rel+': '+('present' if path.is_file() and path.read_text().strip() else 'missing/empty'))
