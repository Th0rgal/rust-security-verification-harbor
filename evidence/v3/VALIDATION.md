# Lean-native v3 validation (2026-10-02)

The two generated tasks use byte-identical prompts and task-specific original
Rust/Lean models. Harbor 0.9.0 with Docker Compose v2 and separate offline
verifiers accepted both oracle references at 1.00, with no trial exceptions.
See harbor/summary.json and the two reference details files for actual results
and prompt hashes. Local reference details also record 1.00; both empty skeletons
score 0.00.

The complete suite also passes as root in the rebuilt verifier Docker image:
`docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier security-verifier:v3-review python3 /repo/scripts/selftest.py`.
The final output is `selftest v3: PASS`. Generated family APIs are beneath a
0755 temporary parent so uid 65534 can traverse them after the verifier's
privilege drop; production sandbox permissions are unchanged.

The adversarial selftest accepts 11 equivalent Rust repairs and rejects six
incorrect repairs universally and concretely. Unsupported production syntax is
rejected before execution. Lean spec cases cover commutativity, guarded Nat
subtraction, if, helper definitions, let, negation, implication, and UInt64
identity helpers; wrapping UInt64 arithmetic remains unsupported in specs.
All-False specs receive only one quarter of the spec checkpoint; empty output
fails coherence and credited exactness. Incorrect/weak/strict specs produce
counterexamples. Unsupported output preserves supported acceptance scores.
Injected solver unknown/timeout never earns success.

Both reference proof terms pass without omega. Invalid types, sorry, added or
tactic-injected axioms, forbidden imports and writes outside the sandbox are
rejected. Malformed spec does not gate vulnerable verdict/witness/patch scores.
Safe verdict without valid evidence earns no verdict/response score. Safe optional
artifacts are inspected by metadata only: binary, oversized, direct symlink and
parent symlink tests pass for both witness and repair paths.

The old GLM 5.3 Flash 0.60 result belongs to v2 JSON grading. No fresh native-Lean
GLM result is included. The spec translator covers a finite Lean fragment;
arbitrary Lean is unsupported with no automated fallback. Lean evidence concerns
the original visible model and submitted spec; repaired Rust and original/model
correspondence are separate trusted SMT/backend obligations, not a Lean compiler
correctness proof.

## Mathlib + RVB `too_complex` expansion (2026-10-07)

Three additional symmetric task pairs (`goldilocks`, `whirlpool`, `plonky3`) were
added from functions in the `rust-verification-benchmark` upstream repositories
(`Winterfell`, `Orca Whirlpools`, `Plonky3`) that had been excluded from RVB as
`too_complex`. Both agent and verifier images now include precompiled `Mathlib`,
`Batteries`, `Aesop`, `Qq`, `Std`, and `Init` (`paloma/lean4-31-rvb-deps:latest`),
and the verifier supports recursive Lean definition unfolding, general `Nat.mul`,
variable-divisor `Nat.div`/`Nat.mod`, Euclidean Z3 purification for large/variable
divisors, and bitwise/shift/tuple-destructuring Rust symbolic semantics.

All 14 reference solutions and skeletons pass `scripts/selftest.py` (`selftest v3: PASS`,
recorded in `evidence/v3/*-reference.json`). Full Harbor 0.9.0 evaluations across
all 12 tasks (`24` trials total) were completed for `claude-opus-5-5` (12/12 at `1.00`)
and `gpt-6.1-sol-high` (11/12 at `1.00`, scoring `0.25` on `plonky3-safe` after
exhausting 25 turns on the 64-bit BabyBear Montgomery reduction Lean proof).

