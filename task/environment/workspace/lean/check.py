#!/usr/bin/env python3
"""Local Lean compilation check; isolated grading remains authoritative."""
from pathlib import Path
import os
import subprocess
import tempfile
root=Path(__file__).resolve().parent
submission=root.parent/'submission'
with tempfile.TemporaryDirectory(prefix='local-lean-') as raw:
    tmp=Path(raw)
    env={**os.environ,'LEAN_PATH':str(root)+':'+str(tmp)}
    for name,rel in [('CandidateSpec','Spec.lean'),('CandidateAudit','Audit.lean')]:
        (tmp/(name+'.lean')).write_text('import SecurityChallenge\n'+(submission/rel).read_text())
        subprocess.run(['lean','-o',name+'.olean',name+'.lean'],cwd=tmp,env=env,check=True)
    proof='import SecurityChallenge\nimport CandidateSpec\nimport CandidateAudit\nimport Lean\nimport Std\nopen SecurityChallenge\ntheorem auditEvidence : AuditClaim candidateSpec verdict := (\n'+(submission/'Proof.lean').read_text()+'\n)\n'
    (tmp/'CandidateProof.lean').write_text(proof)
    raise SystemExit(subprocess.call(['lean','CandidateProof.lean'],cwd=tmp,env=env))
