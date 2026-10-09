# Rust Security Verification Harbor

Each task in this benchmark gives an agent a real-world 64-bit multi-module Rust arithmetic and clearing engine without telling it whether the crate is safe or buggy. Every problem exists as a symmetric pair of Harbor tasks (`-vulnerable` and `-safe`) with the exact same prompt and 37 passing unit and integration tests.

Instead of giving the model a pre-written theorem statement or pointing to a specific function, we ask the model to audit the full crate, write its own formal specification and universal Lean 4.31 soundness proof, and grade the submission automatically in three steps:

1. **Specification (`Spec.lean`, `0.25`):**
   The model formalizes what `authorize(balance, amount, fee)` should compute in unbounded `Nat` arithmetic (where 64-bit machine overflow cannot happen) by tracing the protocol contract across the crate modules. Because the model writes `Spec.lean` itself, a naive Lean checker could be gamed by a vacuous spec (`False`) or by copying the buggy `u64` implementation into the spec. To prevent this while accepting any valid mathematical formulation, our Lean 4.31 metaprogram (`SpecAudit.lean`) unfolds the submitted spec into a normalized arithmetic AST, and `spec.py` uses Z3 (`QF_NIA` with Euclidean quotient/remainder and bitwise lane purification) to verify semantic equivalence over all $2^{64} \times 2^{64} \times 2^{64}$ inputs across four facets (safety, completeness, output exactness, and non-vacuity).

2. **Audit & Universal Lean 4.31 Proof (`Audit.lean` + `Proof.lean`, `0.40`):**
   The model declares `.safe` or `.vulnerable` (`0.15`) and proves `AuditClaim candidateSpec verdict` (`0.25`), which requires a **universal conformity proof** (`Conforms candidateSpec challengeAuthorize`) on **both** variants, checked from scratch by `leanchecker --fresh` (no `sorry`, custom `axiom`, `native_decide`, or `bv_decide`):
   - **If `.safe`:** Proves universal conformity of the original multi-module Lean model (`LeanModel/*.lean`).
   - **If `.vulnerable`:** Proves universal conformity of the repaired Lean model after surgically patching the defective low-level arithmetic module in `/workspace/submission/LeanModel/`.

3. **Resolution (`counterexample.json` + `src/*.rs` + `LeanModel/*.lean`, `0.35`):**
   - **If `.safe`:** The universal Lean 4.31 proof in Step 2 completes the task alongside universal Z3 symbolic verification (`rust_symbolic.py`) of the pristine crate.
   - **If `.vulnerable`:** The model provides a concrete input (`counterexample.json`, `0.15`) that breaks the compiled pristine Rust binary (`rustc -O`), plus a surgical pure-`u64` Rust repair (`/workspace/submission/src/*.rs`, `0.20`) and repaired Lean module (`/workspace/submission/LeanModel/*.lean`) that pass universal Z3 symbolic equivalence (`rust_symbolic.py`) and the universal Lean 4.31 soundness proof.

---

## Flagship Benchmark (`zk-clearing`) & Results

By default (`python3 scripts/make-family.py /tmp/security-family`), the benchmark generates the flagship symmetric pair (**2 Harbor tasks: `zk-clearing-vulnerable` and `zk-clearing-safe`**) from **[`problems/zk-clearing`](problems/zk-clearing)**:
- **Codebase Scale:** `1,528` lines of pure-`u64` Rust across `11` modules in `src/` (`constants.rs`, `word_math.rs`, `reciprocal_div.rs`, `broadword_swar.rs`, `montgomery_field.rs`, `goldilocks_field.rs`, `fee_schedule.rs`, `liquidity_pool.rs`, `transcript_codec.rs`, `clearing_pipeline.rs`, `lib.rs`) with `37` unit tests, paired with `10` Lean 4.31 modules in `LeanModel/` (`633` LOC) and `SecurityChallenge.lean`.
- **Coupled Multi-Module Architecture:** Every clearing transaction sums principal `amount` with four distinct 64-bit arithmetic surcharges (basis-point ceiling fee with 10% floor rebate via `word_math` + `fee_schedule`, Möller-Granlund 2-by-1 reciprocal division slot quotient via `reciprocal_div`, Vigna SWAR broadword byte-lane surcharge via `broadword_swar`, and Plonky3 BabyBear Montgomery reduction levy via `montgomery_field`) surrounded by realistic sibling modules (`goldilocks_field`, `liquidity_pool`, `transcript_codec`).
- **Hidden Vulnerability in `.vulnerable`:** Inside `word_math::ceil_div_bps_u64`, the non-carry `biased < sum.low_word` wrap branch (`2^64 - 9999 <= amount + fee <= 2^64 - 1`) folds `biased + U64_MOD_BPS_REM` instead of `(sum.low_word % BPS_DENOM) + BPS_MAX_REM`, under-computing the gross basis-point fee by `1` across an interior carry pocket while remaining exact at `0`, ordinary values, and `u64::MAX`.

We evaluate frontier models in Harbor 0.9.0 (`terminus-2`, `reasoning_effort=high`) under a **10-turn budget (`max_turns=10`)** and an **extended 25-turn budget (`max_turns=25`)**:

| Flagship Benchmark (`zk-clearing`, 2 Tasks) | Claude Opus 5.5 (`high`) @ **10T** | Claude Opus 5.5 (`high`) @ **25T** | GPT 6.1 Sol (`high`) @ **10T** | GPT 6.1 Sol (`high`) @ **25T** | Reference Oracle |
|---|---:|---:|---:|---:|---:|
| **`zk-clearing-vulnerable`** | **0.000** | **0.000** | **0.000** | **0.250** | **1.000** |
| **`zk-clearing-safe`** | **0.000** | **0.000** | **0.000** | **0.250** | **1.000** |
| **Overall Mean (`2` tasks)** | **0.000** (`0.00 / 2`) | **0.000** (`0.00 / 2`) | **0.000** (`0.00 / 2`) | **0.250** (`0.50 / 2`) | **1.000** (`2.00 / 2`) |

*(Passing `--problem all` to `scripts/make-family.py` or `--all` to `scripts/summarize-results.py` also includes the 9 single-kernel calibration pairs: `ruint`, `succinct`, `plonky3`, `settlement-engine`, `whirlpool`, `goldilocks`, `settlement-modular`, `settlement`, and `openpql`.)*

- **Specification formula, per-task token/turn breakdown, failure analysis, and calibration suite results:** [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md)
- **Verifier architecture and AST lowering details:** [BACKEND.md](BACKEND.md)

---

## Quick Start

```bash
# 1. Print the @10T vs @25T summary table from the committed Harbor traces:
python3 scripts/summarize-results.py

# 2. Generate the flagship zk-clearing Harbor task pair into /tmp/security-family:
python3 scripts/make-family.py /tmp/security-family

# 3. Run a Harbor evaluation on either generated task:
harbor run -p /tmp/security-family/zk-clearing-vulnerable \
  -a terminus-2 -m <model> \
  --ak reasoning_effort=high --ak max_turns=25 -e docker -n 1
```
