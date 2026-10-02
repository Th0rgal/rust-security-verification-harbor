# Rust security prove-or-refute Harbor

One deliberately difficult training environment derived from the structure of
the [Rust Verification Benchmark](https://github.com/lfglabs-dev/rust-verification-benchmark-harbor).
The agent receives a realistic vulnerable Rust payment authorizer, but no Lean
model. It must recover the security property, exhibit the overflow exploit,
repair Rust, and prove the repair.

## Curriculum and reward

| checkpoint | submitted artifact | verifier evidence | reward |
|---|---|---|---:|
| 1. Specify | `submission/spec.json` | canonical machine-readable invariant | 0.20 |
| 2. Refute | `submission/counterexample.json` | runs against pristine vulnerable code | 0.25 |
| 3. Repair | `submission/src/lib.rs` | compile + oracle, boundary, metamorphic tests | 0.25 |
| 4. Prove | `submission/Proof.lean` | Lean kernel checks the repaired theorem | 0.30 |

Scores are cumulative and partial: `0`, `.20`, `.45`, `.70`, or `1.00`. The
verifier is a separate container and uses pristine sources. The agent cannot
alter tests or the hidden Lean model. Checkpoints prevent a lucky proof from
skipping vulnerability discovery.

```bash
pip install harbor==0.9.0
# Authenticate to ghcr.io for the source benchmark's pinned Lean dependency image.
harbor run -p task -a <agent> -m <model> -e docker
```

For development without Harbor: `python3 scripts/selftest.py`. Docker/Lean is
tested separately with `docker build -f task/tests/Dockerfile task/tests`.

## What Harbor does here

`task/task.toml` declares the agent image, isolated verifier, timeouts, and the
four artifacts Harbor copies from `/workspace`. `instruction.md` is the staged
harness prompt: it nudges invariant → exploit → patch → proof, while exposing
only the Rust code and a proof skeleton. `tests/test.sh` computes the scalar
reward and writes `/logs/verifier/{reward.txt,details.json}`.

The bug is intentionally exploitable: release-mode `u64` wrapping lets a debit
near `u64::MAX` appear affordable. The scenario models a service that checks a
ledger amount before handing it to a wider settlement backend. Never deploy
the code.
