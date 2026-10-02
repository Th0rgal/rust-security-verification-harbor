#!/usr/bin/env python3
from __future__ import annotations
import json, shutil, subprocess, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TASK = ROOT / "task"

def grade(workspace: Path, logs: Path) -> float:
    cmd = ["python3", str(TASK/"tests/verifier/verify.py"), "--workspace", str(workspace),
           "--verifier", str(TASK/"tests/verifier"), "--logs", str(logs)]
    done = subprocess.run(cmd, text=True, capture_output=True)
    if done.returncode: raise RuntimeError(done.stdout + done.stderr)
    return float((logs/"reward.txt").read_text())

def main() -> None:
    with tempfile.TemporaryDirectory(prefix="harbor-selftest-") as raw:
        root = Path(raw); workspace = root/"workspace"; logs = root/"logs"
        shutil.copytree(TASK/"environment/workspace", workspace)
        assert grade(workspace, logs) == 0.0
        shutil.copy(TASK/"solution/spec.json", workspace/"submission/spec.json")
        assert grade(workspace, logs) == 0.20
        shutil.copy(TASK/"solution/counterexample.json", workspace/"submission/counterexample.json")
        assert grade(workspace, logs) == 0.45
        shutil.copy(TASK/"solution/src/lib.rs", workspace/"submission/src/lib.rs")
        assert grade(workspace, logs) == 0.70
        shutil.copy(TASK/"solution/Proof.lean", workspace/"submission/Proof.lean")
        assert grade(workspace, logs) == 1.0
        details = json.loads((logs/"details.json").read_text())
        assert all(x["passed"] for x in details["checkpoints"].values())
    print("selftest: rewards 0.00 → 0.20 → 0.45 → 0.70 → 1.00")

if __name__ == "__main__": main()
