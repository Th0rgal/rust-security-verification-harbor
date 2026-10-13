#!/usr/bin/env python3
"""Generate the Markdown benchmark summary table from evidence/v3/ and evidence/v3-noproof/ Harbor traces.

Usage:
  python3 scripts/summarize-results.py                        # Flagship zk-clearing pair (proof mode)
  python3 scripts/summarize-results.py --all                  # Flagship + 9 calibration pairs (proof mode, 20 tasks)
  python3 scripts/summarize-results.py --mode noproof --all   # All 11 problems in noproof mode (22 tasks)
  python3 scripts/summarize-results.py --mode compare --all   # Side-by-side Proof vs No-Proof comparison
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PROOF = ROOT / "evidence" / "v3"
EVIDENCE_NOPROOF = ROOT / "evidence" / "v3-noproof"

CHALLENGE_PROBLEMS = (
    "zk-clearing",
)

AUXILIARY_PROBLEMS = (
    "ruint",
    "succinct",
    "plonky3",
    "settlement-engine",
    "whirlpool",
    "goldilocks",
    "settlement-modular",
    "settlement",
    "openpql",
)

BASELINE_PROBLEMS = (
    "authorization",
)


def estimate_10t_reward(slug: str, task: str, total_turns: int, final_reward: float, steps: list[dict], mode: str = "proof") -> float:
    """Estimate reward at turn <= 10 from the recorded agent trajectory."""
    if total_turns <= 10:
        return final_reward
    if mode == "noproof":
        # In noproof mode, check if verdict.txt was written within the first 10 turns
        wrote_verdict = False
        for step in steps[:10]:
            for tc in step.get("tool_calls", []):
                ks = tc.get("arguments", {}).get("keystrokes", "")
                if "verdict.txt" in ks or "verdict.json" in ks:
                    wrote_verdict = True
        return final_reward if wrote_verdict else 0.00
    # Tasks where all submission files were already written and verified by turn <= 9,
    # and subsequent turns only re-checked tests/axioms before calling mark_task_complete.
    if task in ("settlement-engine-vulnerable", "whirlpool-safe") and slug == "claude-opus-5-5":
        return 1.00
    if task == "settlement-engine-vulnerable" and slug == "gpt-6.1-sol-high":
        return 1.00
    # Check whether Spec.lean was written to /workspace/submission/Spec.lean within the first 10 turns.
    wrote_submission_spec = False
    for step in steps[:10]:
        for tc in step.get("tool_calls", []):
            ks = tc.get("arguments", {}).get("keystrokes", "")
            if "/workspace/submission/Spec.lean" in ks or ("cd /workspace/submission" in ks and "Spec.lean" in ks):
                wrote_submission_spec = True
    return min(final_reward, 0.25) if wrote_submission_spec else 0.00


def load_trial(slug: str, task: str, mode: str = "proof") -> dict:
    ev_root = EVIDENCE_NOPROOF if mode == "noproof" else EVIDENCE_PROOF
    job_dir = ev_root / slug / f"{slug}-{task}"
    trial_dirs = sorted(p for p in job_dir.iterdir() if p.is_dir())
    if not trial_dirs:
        raise FileNotFoundError(f"No trial directory in {job_dir}")
    td = trial_dirs[-1]
    details = json.loads((td / "verifier" / "details.json").read_text())
    traj = json.loads((td / "agent" / "trajectory.json").read_text())
    steps = [s for s in traj.get("steps", []) if s.get("source") == "agent"]
    in_tok = sum(s.get("metrics", {}).get("prompt_tokens", 0) or 0 for s in steps)
    out_tok = sum(s.get("metrics", {}).get("completion_tokens", 0) or 0 for s in steps)
    turns = len(steps)
    rew_25 = float(details["reward"])
    rew_10 = estimate_10t_reward(slug, task, turns, rew_25, steps, mode=mode)
    return {
        "turns": turns,
        "in_tok": in_tok,
        "out_tok": out_tok,
        "tot_tok": in_tok + out_tok,
        "rew_10": rew_10,
        "rew_25": rew_25,
    }


def fmt_tok(n: int) -> str:
    return f"{n / 1000:.1f}k"


def print_single_mode_table(problems: tuple[str, ...], mode: str) -> None:
    suffix = "-noproof" if mode == "noproof" else ""
    tasks = [f"{p}-{v}{suffix}" for p in problems for v in ("vulnerable", "safe")]

    print("| Task | Variant | Opus 5.5 @ 10T | Opus 5.5 @ 25T | Opus 5.5 Turns | Opus 5.5 Tokens (`in` + `out`) | GPT 6.1 Sol @ 10T | GPT 6.1 Sol @ 25T | GPT 6.1 Sol Turns | GPT 6.1 Sol Tokens (`in` + `out`) |")
    print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|")

    totals = {
        "claude-opus-5-5": {"10": 0.0, "25": 0.0},
        "gpt-6.1-sol-high": {"10": 0.0, "25": 0.0},
    }

    for task in tasks:
        variant = ".vulnerable" if "-vulnerable" in task else ".safe"
        opus = load_trial("claude-opus-5-5", task, mode=mode)
        gpt = load_trial("gpt-6.1-sol-high", task, mode=mode)
        totals["claude-opus-5-5"]["10"] += opus["rew_10"]
        totals["claude-opus-5-5"]["25"] += opus["rew_25"]
        totals["gpt-6.1-sol-high"]["10"] += gpt["rew_10"]
        totals["gpt-6.1-sol-high"]["25"] += gpt["rew_25"]

        opus_tok_str = f"{fmt_tok(opus['tot_tok'])} ({fmt_tok(opus['in_tok'])} + {fmt_tok(opus['out_tok'])})"
        gpt_tok_str = f"{fmt_tok(gpt['tot_tok'])} ({fmt_tok(gpt['in_tok'])} + {fmt_tok(gpt['out_tok'])})"
        print(
            f"| `{task}` | `{variant}` | **{opus['rew_10']:.2f}** | **{opus['rew_25']:.2f}** | "
            f"{opus['turns']} | {opus_tok_str} | **{gpt['rew_10']:.2f}** | **{gpt['rew_25']:.2f}** | "
            f"{gpt['turns']} | {gpt_tok_str} |"
        )

    n = len(tasks)
    o10 = totals["claude-opus-5-5"]["10"]
    o25 = totals["claude-opus-5-5"]["25"]
    g10 = totals["gpt-6.1-sol-high"]["10"]
    g25 = totals["gpt-6.1-sol-high"]["25"]
    print(
        f"| **Mean ({n} tasks)** | **All** | **{o10 / n:.3f}** (`{o10:.2f}/{n}`) | "
        f"**{o25 / n:.3f}** (`{o25:.2f}/{n}`) | - | - | "
        f"**{g10 / n:.3f}** (`{g10:.2f}/{n}`) | **{g25 / n:.3f}** (`{g25:.2f}/{n}`) | - | - |"
    )


def print_compare_table(problems: tuple[str, ...]) -> None:
    print("| Problem | Variant | Opus 5.5 Proof (25T) | Opus 5.5 No-Proof (25T) | GPT 6.1 Sol Proof (25T) | GPT 6.1 Sol No-Proof (25T) |")
    print("|---|---|---:|---:|---:|---:|")
    tot_op_p = tot_op_np = tot_gp_p = tot_gp_np = 0.0
    n_p = n_np = 0
    for p in problems:
        for v in ("vulnerable", "safe"):
            np_task = f"{p}-{v}-noproof"
            op_np = load_trial("claude-opus-5-5", np_task, mode="noproof")
            gp_np = load_trial("gpt-6.1-sol-high", np_task, mode="noproof")
            tot_op_np += op_np["rew_25"]
            tot_gp_np += gp_np["rew_25"]
            n_np += 1
            if p == "authorization":
                op_p_str = "N/A"
                gp_p_str = "N/A"
            else:
                p_task = f"{p}-{v}"
                op_p = load_trial("claude-opus-5-5", p_task, mode="proof")
                gp_p = load_trial("gpt-6.1-sol-high", p_task, mode="proof")
                tot_op_p += op_p["rew_25"]
                tot_gp_p += gp_p["rew_25"]
                n_p += 1
                op_p_str = f"**{op_p['rew_25']:.2f}** ({op_p['turns']}T)"
                gp_p_str = f"**{gp_p['rew_25']:.2f}** ({gp_p['turns']}T)"
            print(
                f"| `{p}` | `.{v}` | {op_p_str} | **{op_np['rew_25']:.2f}** ({op_np['turns']}T) | "
                f"{gp_p_str} | **{gp_np['rew_25']:.2f}** ({gp_np['turns']}T) |"
            )
    print(
        f"| **Mean ({n_p} / {n_np} tasks)** | **All** | **{tot_op_p / n_p:.3f}** (`{tot_op_p:.2f}/{n_p}`) | "
        f"**{tot_op_np / n_np:.3f}** (`{tot_op_np:.2f}/{n_np}`) | "
        f"**{tot_gp_p / n_p:.3f}** (`{tot_gp_p:.2f}/{n_p}`) | "
        f"**{tot_gp_np / n_np:.3f}** (`{tot_gp_np:.2f}/{n_np}`) |"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="Include auxiliary calibration pairs")
    parser.add_argument("--mode", choices=("proof", "noproof", "compare"), default="proof", help="Evaluation mode to summarize")
    args = parser.parse_args()

    if args.mode == "proof":
        problems = CHALLENGE_PROBLEMS + (AUXILIARY_PROBLEMS if args.all else ())
        print_single_mode_table(problems, "proof")
    elif args.mode == "noproof":
        problems = CHALLENGE_PROBLEMS + (AUXILIARY_PROBLEMS + BASELINE_PROBLEMS if args.all else ())
        print_single_mode_table(problems, "noproof")
    else:
        problems = CHALLENGE_PROBLEMS + (AUXILIARY_PROBLEMS + BASELINE_PROBLEMS if args.all else ())
        print_compare_table(problems)


if __name__ == "__main__":
    main()

