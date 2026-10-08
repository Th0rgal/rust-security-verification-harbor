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

All 20 reference solutions and skeletons pass `scripts/selftest.py` (`selftest v3: PASS`,
recorded in `evidence/v3/*-reference.json`).

## Challenge Benchmark curation and 10-turn default horizon (2026-10-08)

To provide a non-redundant difficulty gradient without easy or duplicate tasks,
`scripts/make-family.py` and `scripts/harbor-smoke.py` now default to `--problem challenge`,
which generates the **6 core Challenge pairs (`12` Harbor tasks)**:
`settlement-engine`, `goldilocks`, `whirlpool`, `plonky3`, `succinct`, and `ruint`
(while `--problem all` retains `authorization`, `settlement`, `settlement-modular`,
and `openpql` for regression testing).

The recommended default agent budget is **`max_turns=10`** (`recommended_max_turns = 10`
in `task/task.toml`), paired with an extended **`max_turns=25`** analysis:
- **At 10 turns (`max_turns=10`)**: Both `claude-opus-5-5` and `gpt-6.1-sol-high` solve
  `6/6` `.vulnerable` tasks (`1.000`), but on `.safe` universal Lean 4 proof tasks
  `claude-opus-5-5` scores `0.375` (`2.25/6`, overall mean `0.688`) and `gpt-6.1-sol-high`
  scores `0.250` (`1.50/6`, overall mean `0.625`).
- **At 25 turns (`max_turns=25`)**: `claude-opus-5-5` solves `12/12` Challenge tasks (`1.000`,
  and `18/18` across all benchmarked tasks), whereas `gpt-6.1-sol-high` reaches `0.813`
  (`9.75/12` on the Challenge suite, `15/18` overall), failing at `0.25` on three `.safe`
  universal Lean 4 proof tasks:
  - `plonky3-safe`: exhausted 25 turns on the 64-bit BabyBear Montgomery reduction Lean proof (`by sorry`).
  - `succinct-safe` (Non-Web3 SWAR broadword kernel from `tov/succinct-rs`): exhausted 25 turns and left a `bv_decide` helper rejected by the transitive axiom auditor (`count_correct._native.bv_decide.ax_1_5`).
  - `ruint-safe` (Web3 Möller-Granlund 2-by-1 normalized division kernel from `alloy-rs/ruint`): exhausted 25 turns unable to discharge the universal `omega` proof over the reciprocal approximation (`D = 32771`, `V = 65524`).



