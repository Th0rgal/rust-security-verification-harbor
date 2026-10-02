#!/usr/bin/env python3
"""Materialize Harbor tasks from one shared kernel. Generated copies are not source."""
import argparse
from pathlib import Path
import shutil
import re

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(); p.add_argument('output',type=Path); args=p.parse_args()
for profile in ('integrated','specify','refute','repair','prove'):
    task = args.output/f'overflow-{profile}'
    if task.exists(): raise SystemExit(f'refusing to overwrite {task}')
    shutil.copytree(ROOT/'task',task,ignore=shutil.ignore_patterns('.lake','__pycache__','target','LocalProof.lean'))
    manifest=task/'task.toml'
    manifest.write_text(manifest.read_text().replace('lfglabs/rust-security-overflow-prove-or-refute',f'lfglabs/rust-security-overflow-{profile}'))
    if profile!='integrated':
        rel = {'specify':'spec.json', 'refute':'counterexample.json', 'repair':'src/lib.rs', 'prove':'Proof.lean'}[profile]
        text = re.sub(r'artifacts = \[.*?\]', 'artifacts = ["/workspace/submission/'+rel+'"]', manifest.read_text(), flags=re.S)
        text = text.replace('[verifier]', '[verifier]\nenv = { GRADER_PROFILE = "'+profile+'" }')
        manifest.write_text(text)
        (task/'solution/solve.sh').write_text('#!/usr/bin/env bash\nset -euo pipefail\ncp /solution/'+rel+' /workspace/submission/'+rel+'\n')
        prompt=task/'instruction.md'
        prompt.write_text(f'# Focus checkpoint: {profile}\n\nOnly **{profile}** contributes to this task’s reward (1.00). Other artifact\nverdicts remain diagnostic and never lock this checkpoint. Follow its contract\nbelow; run the harness with `--profile {profile}`.\n\n'+prompt.read_text())
    if profile in ('specify', 'refute'):
        # Discovery tasks never ship a repaired authorizer or its Lean signature.
        shutil.rmtree(task/'environment/workspace/lean')
        (task/'environment/workspace/submission/Proof.lean').unlink()
        docker = task/'environment/Dockerfile'
        text = docker.read_text()
        text = text[text.index('FROM rust:'):]
        text = text.replace('COPY --from=lean /opt/lean/ /opt/lean/\n', '')
        text = text.replace('ENV PATH="/opt/lean/bin:${PATH}" LEAN_PATH=/workspace/lean\n', '')
        text = text.replace(' \\\n && cd /workspace/lean && lean Signature.lean', '')
        docker.write_text(text)
        harness = task/'environment/workspace/harness/checkpoint.py'
        text = harness.read_text().replace("default='integrated'", "default='"+profile+"'")
        # Do not leave answer-bearing hints for other stages in discovery images.
        text = text.replace("'repair':'Preserve the API and return Some exactly when the mathematical total is affordable.'", "'repair':'Review the submitted implementation.'")
        text = text.replace("'refute':'Find a pristine release-Rust authorization whose mathematical total exceeds balance.'", "'refute':'Reproduce a security violation against the pristine challenge.'")
        harness.write_text(text)
        discovery = """# Discover the settlement contract

Audit `/workspace/challenge` using its code and service policy. Recover the
intended mathematical contract and identify a concrete security violation.
The verifier uses pristine sources; editing the challenge cannot change it.
"""
        if profile == 'specify':
            discovery += """
Write `/workspace/submission/spec.json`. Typed DSL v2 uses `version:2` and a
boolean `accept` expression. Optional clauses describe `total_debit` (unsigned
expression), `on_overflow` and `completeness`; see `spec.schema.json` for grammar.
Each of affordability/safety, exact successful output, explicit overflow policy
and completeness earns 0.25 of this checkpoint's reward. Arithmetic is
mathematical, inputs are u64, constants are unsigned u128, and the verifier
limits expressions to 64 nodes total and depth 12. It checks non-vacuity,
reference validity, safety adequacy and equivalence separately.
"""
        else:
            discovery += """
Write `/workspace/submission/counterexample.json`: exactly the decimal JSON
integer keys `balance`, `amount`, `fee`, all within u64. The verifier executes
the pristine release-mode implementation and checks the reproduced violation.
"""
        discovery += f"\nOnly **{profile}** contributes to reward. Run `python3 /workspace/harness/checkpoint.py --profile {profile}` for advisory readiness.\n"
        (task/'instruction.md').write_text(discovery)
    print(task)
