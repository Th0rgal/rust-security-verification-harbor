#!/usr/bin/env python3
"""Local proof convenience runner. The isolated grader remains authoritative."""
from pathlib import Path
import os
import subprocess
root = Path(__file__).resolve().parent
signature = (root/'Signature.lean').read_text().split(':=\nby')[0]
term = (root.parent/'submission/Proof.lean').read_text()
candidate = root/'LocalProof.lean'
candidate.write_text(signature + ':= (\n' + term + '\n)\n')
raise SystemExit(subprocess.call(['lean', str(candidate)], cwd=root,
    env={**os.environ, 'LEAN_PATH':str(root)}))
