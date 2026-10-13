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
- **Codebase Scale:** `1,540` lines of pure-`u64` Rust across `11` modules in `src/` (`constants.rs`, `word_math.rs`, `reciprocal_div.rs`, `broadword_swar.rs`, `montgomery_field.rs`, `goldilocks_field.rs`, `fee_schedule.rs`, `liquidity_pool.rs`, `transcript_codec.rs`, `clearing_pipeline.rs`, `lib.rs`) with `37` unit tests, paired with `10` Lean 4.31 modules in `LeanModel/` (`676` LOC) and `SecurityChallenge.lean` (`1,046` LOC in `Proof.lean`).
- **6-Stage All-10-Module Coupled Architecture:** Every clearing transaction couples all 10 domain modules into `total_debit = amount + base_surcharge + bridge_surcharge` without a top-level formula cheat-sheet:
  1. Basis-point ceiling fee with 10% floor tier rebate (`word_math` + `fee_schedule`)
  2. Flash-settlement LP reserve retention with 25% floor treasury cut (`word_math` + `liquidity_pool`)
  3. Möller-Granlund 2-by-1 reciprocal division blob slot quotient (`reciprocal_div`)
  4. Vigna SWAR broadword byte-lane surcharge (`broadword_swar`)
  5. Plonky3 BabyBear Montgomery reduction prover levy (`montgomery_field`)
  6. Sequencer transcript domain tag surcharge (`transcript_codec`) + Goldilocks 128-bit field reduction bridge surcharge (`goldilocks_field`)
- **Hidden Vulnerability & Cross-Module Counterexample Coupling in `.vulnerable`:** While `word_math::ceil_div_bps_u64` (`10_000`) is completely sound (acting as a realistic decoy), `word_math::ceil_div_flash_u64` (`5_000`) folds `biased + U64_MOD_FLASH_REM` in its non-carry `biased < sum.low_word` wrap branch (`2^64 - 4999 <= amount + fee <= 2^64 - 1617`), under-computing the flash LP surcharge across a 3,383-wide interior pocket. Because `bridge_surcharge = (amount + fee * 2^64) mod P_GL` exceeds `2^64 - 7e12` for small `amount` in that pocket, naive `amount = 0` boundary probes always overflow `u64::MAX`; constructing a valid counterexample requires simultaneously satisfying the `WordMath` pocket and keeping the 128-bit `GoldilocksField` residue small (e.g. `fee = GOLDILOCKS_P`).

We evaluate frontier models in Harbor 0.9.0 (`terminus-2`, `reasoning_effort=high`) across both tracks:
- **Formal Proof Track (`--mode proof`, default):** Requires `Spec.lean` (`25%`), `Audit.lean` (`15%`), `Proof.lean` (`25%`), and `counterexample.json` (`15%`) + repaired Rust/Lean (`20%`) on `.vulnerable`.
- **Direct Security Audit Track without Formal Proof (`--mode noproof`):** Gives the agent a clean Rust workspace without Lean 4 and asks only for an audit verdict (`verdict.txt`: `safe` or `vulnerable`, `20%` gated on justification) and, if `vulnerable`, a concrete `counterexample.json` (`30%`) and repaired pure-`u64` Rust crate (`50%`, verified universally by Z3 `rust_symbolic.py`).

| Flagship Benchmark (`zk-clearing`, 2 Tasks) | Opus 5.5 (`proof` @ 25T) | Opus 5.5 (`noproof` @ 25T) | GPT 6.1 Sol (`proof` @ 25T) | GPT 6.1 Sol (`noproof` @ 25T) | Reference Oracle |
|---|---:|---:|---:|---:|---:|
| **`zk-clearing-vulnerable`** | **0.000** (25T) | **1.000** (24T) | **0.000** (25T) | **0.000** (21T, false `safe`) | **1.000** |
| **`zk-clearing-safe`** | **0.000** (25T) | **1.000** (15T) | **0.000** (25T) | **1.000** (14T) | **1.000** |
| **Flagship Mean (`2` tasks)** | **0.000** (`0.00 / 2`) | **1.000** (`2.00 / 2`) | **0.000** (`0.00 / 2`) | **0.500** (`1.00 / 2`) | **1.000** (`2.00 / 2`) |
| **Full Suite Mean (`20` / `22` tasks)** | **0.900** (`18.00 / 20`) | **1.000** (`22.00 / 22`) | **0.787** (`15.75 / 20`) | **0.909** (`20.00 / 22`) | **1.000** |

*(Passing `--problem all` to `scripts/make-family.py` or `--all` to `scripts/summarize-results.py` includes all calibration pairs across both `proof` and `noproof` modes.)*

- **Specification formula, per-task token/turn breakdown, failure analysis, and `Proof` vs `No-Proof` comparison:** [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md)
- **Verifier architecture and AST lowering details:** [BACKEND.md](BACKEND.md)

---

## Quick Start

```bash
# 1. Print the summary tables (proof, noproof, or side-by-side comparison):
python3 scripts/summarize-results.py --all
python3 scripts/summarize-results.py --mode noproof --all
python3 scripts/summarize-results.py --mode compare --all

# 2. Generate the flagship zk-clearing Harbor task pairs (proof, noproof, or both):
python3 scripts/make-family.py /tmp/security-family --mode both

# 3. Run a Harbor evaluation on a generated task:
harbor run -p /tmp/security-family/zk-clearing-vulnerable-noproof \
  -a terminus-2 -m <model> \
  --ak reasoning_effort=high --ak max_turns=25 -e docker -n 1
```

