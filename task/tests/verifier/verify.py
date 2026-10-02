#!/usr/bin/env python3
"""Isolated, cumulative four-stage Harbor verifier."""
from __future__ import annotations

import argparse
import json
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

U64_MAX = 2**64 - 1
WEIGHTS = (0.20, 0.25, 0.25, 0.30)


def load_json(path: Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError("expected a JSON object")
    return value


def check_spec(path: Path) -> str:
    expected = {
        "property": "authorized_total_le_balance",
        "arithmetic": "mathematical_unsigned",
        "on_overflow": "reject",
    }
    if load_json(path) != expected:
        raise ValueError("spec must express the trust-boundary invariant and overflow policy")
    return "canonical security invariant accepted"


def check_counterexample(path: Path) -> str:
    obj = load_json(path)
    if set(obj) != {"balance", "amount", "fee"}:
        raise ValueError("counterexample requires exactly balance, amount, fee")
    balance, amount, fee = (obj[k] for k in ("balance", "amount", "fee"))
    if any(type(x) is not int or not 0 <= x <= U64_MAX for x in (balance, amount, fee)):
        raise ValueError("witness values must be u64 JSON integers")
    mathematical = amount + fee
    wrapped = mathematical & U64_MAX
    if mathematical <= U64_MAX or mathematical <= balance or wrapped > balance:
        raise ValueError("witness does not exploit wrapping to violate the invariant")
    return f"exploit reproduced: mathematical debit {mathematical} authorized as {wrapped}"


def run(cmd: list[str], cwd: Path, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, timeout=timeout)


def check_patch(path: Path) -> str:
    source = path.read_text()
    forbidden = ("unsafe", "wrapping_", "overflowing_", "saturating_", "panic!", "todo!", "unimplemented!")
    if any(token in source for token in forbidden):
        raise ValueError("patch uses a forbidden escape hatch")
    if "pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization>" not in source:
        raise ValueError("public API changed")
    if source.count("pub fn authorize") != 1 or "amount.checked_add(fee)?" not in source:
        raise ValueError("patch must make the modeled checked-addition transition explicit")
    if any(token in source for token in ("#[cfg", "include!", "macro_rules!", "std::process", "std::env")):
        raise ValueError("patch contains environment-dependent or hidden behavior")

    with tempfile.TemporaryDirectory(prefix="security-patch-") as raw:
        tmp = Path(raw)
        (tmp / "lib.rs").write_text(source)
        driver = r'''
extern crate submitted;
use submitted::authorize;
use std::env;
fn main() {
    let a: Vec<u64> = env::args().skip(1).map(|x| x.parse().unwrap()).collect();
    match authorize(a[0], a[1], a[2]) {
        Some(v) => println!("some:{}", v.total_debit),
        None => println!("none"),
    }
}
'''
        (tmp / "driver.rs").write_text(driver)
        compile_lib = run(["rustc", "--edition=2021", "--crate-name", "submitted", "--crate-type=rlib", "-O", "lib.rs"], tmp)
        if compile_lib.returncode:
            raise ValueError("patch does not compile: " + compile_lib.stderr[-1200:])
        compile_driver = run(["rustc", "--edition=2021", "-O", "driver.rs", "--extern", "submitted=libsubmitted.rlib", "-o", "probe"], tmp)
        if compile_driver.returncode:
            raise ValueError("public API is incompatible: " + compile_driver.stderr[-1200:])

        cases = [
            (0, 0, 0), (109, 100, 10), (110, 100, 10),
            (U64_MAX, U64_MAX, 0), (0, U64_MAX, 1),
            (U64_MAX, U64_MAX, 1), (42, U64_MAX - 4, 5),
        ]
        rng = random.Random(0xC0FFEE)
        cases += [(rng.randrange(2**64), rng.randrange(2**64), rng.randrange(2**64)) for _ in range(256)]
        for balance, amount, fee in cases:
            result = run([str(tmp / "probe"), str(balance), str(amount), str(fee)], tmp, 5)
            total = amount + fee
            expected = f"some:{total}" if total <= U64_MAX and total <= balance else "none"
            if result.returncode or result.stdout.strip() != expected:
                raise ValueError(f"oracle mismatch at ({balance}, {amount}, {fee}): expected {expected!r}")
    return f"patch compiled and passed {len(cases)} boundary/oracle tests"


def check_proof(path: Path, verifier: Path) -> str:
    proof = path.read_text().strip()
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|implemented_by|extern)\b")
    if not proof.startswith("by") or forbidden.search(proof):
        raise ValueError("proof must be a tactic term without forbidden declarations")
    candidate = verifier / "Candidate.lean"
    candidate.write_text("""import SecurityChallenge\nimport Mathlib.Tactic\n\nopen SecurityChallenge\n\ntheorem patched_authorize_sound (balance amount fee total : Nat)\n    (h : repairedAuthorize balance amount fee = some total) :\n    amount + fee = total ∧ total ≤ balance :=\n""" + proof + "\n")
    try:
        checked = run(["lake", "env", "lean", "Candidate.lean"], verifier, 120)
    finally:
        candidate.unlink(missing_ok=True)
    if checked.returncode:
        raise ValueError("Lean rejected proof: " + (checked.stdout + checked.stderr)[-1600:])
    return "Lean kernel accepted repaired_authorize_sound"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    args = parser.parse_args()
    submission = args.workspace / "submission"
    checks = [
        ("spec", lambda: check_spec(submission / "spec.json")),
        ("counterexample", lambda: check_counterexample(submission / "counterexample.json")),
        ("patch", lambda: check_patch(submission / "src/lib.rs")),
        ("proof", lambda: check_proof(submission / "Proof.lean", args.verifier)),
    ]
    details: dict[str, object] = {"status": "ok", "checkpoints": {}}
    reward = 0.0
    prior_ok = True
    for (name, check), weight in zip(checks, WEIGHTS):
        if not prior_ok:
            details["checkpoints"][name] = {"passed": False, "detail": "locked by previous checkpoint"}
            continue
        try:
            message = check()
            reward += weight
            details["checkpoints"][name] = {"passed": True, "detail": message}
        except Exception as exc:
            prior_ok = False
            details["checkpoints"][name] = {"passed": False, "detail": str(exc)}
    args.logs.mkdir(parents=True, exist_ok=True)
    (args.logs / "reward.txt").write_text(f"{reward:.2f}\n")
    details["reward"] = round(reward, 2)
    (args.logs / "details.json").write_text(json.dumps(details, indent=2) + "\n")
    print(json.dumps(details, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
