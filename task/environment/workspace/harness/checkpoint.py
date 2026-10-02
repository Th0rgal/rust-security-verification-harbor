#!/usr/bin/env python3
"""Public curriculum guide; authoritative checks remain in the verifier."""
import json
from pathlib import Path

root = Path("/workspace/submission")
def object_at(name):
    try:
        return json.loads((root / name).read_text())
    except Exception:
        return {}

if not object_at("spec.json"):
    print("CHECKPOINT 1 · Specify: distinguish mathematical addition from u64 execution.")
elif not object_at("counterexample.json"):
    print("CHECKPOINT 2 · Refute: seek a+b > u64::MAX whose wrapped result fits balance.")
elif "checked_add" not in (root / "src/lib.rs").read_text():
    print("CHECKPOINT 3 · Repair: reject overflow before comparing the exact total.")
elif "sorry" in (root / "Proof.lean").read_text():
    print("CHECKPOINT 4 · Prove: unfold, split the successful branch, then use omega.")
else:
    print("All artifacts populated. Submit for isolated verification.")
