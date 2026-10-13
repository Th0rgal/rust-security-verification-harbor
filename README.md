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

We evaluate frontier models in Harbor 0.9.0 (`terminus-2`, `reasoning_effort=high`) at `10` turns (fast budget) and `25` turns (extended budget), alongside our deterministic reference oracle:

| Flagship Benchmark (`zk-clearing`, 2 Tasks) | Claude Opus 5.5 (`10` Turns) | Claude Opus 5.5 (`25` Turns) | GPT 6.1 Sol (`10` Turns) | GPT 6.1 Sol (`25` Turns) | Reference Oracle |
|---|---:|---:|---:|---:|---:|
| **`zk-clearing-vulnerable`** | **0.000** | **0.000** | **0.000** | **0.000** | **1.000** |
| **`zk-clearing-safe`** | **0.000** | **0.000** | **0.000** | **0.000** | **1.000** |
| **Flagship Mean (`2` tasks)** | **0.000** (`0.00 / 2`) | **0.000** (`0.00 / 2`) | **0.000** (`0.00 / 2`) | **0.000** (`0.00 / 2`) | **1.000** (`2.00 / 2`) |
| **Full Suite Mean (`20` tasks, `--all`)** | **0.588** (`11.75 / 20`) | **0.900** (`18.00 / 20`) | **0.487** (`9.75 / 20`) | **0.787** (`15.75 / 20`) | **1.000** (`20.00 / 20`) |

---

## Why Formal Verification? False Positive & False Negative Ablation (`Proof` vs. `No-Proof`)

When we remove the Lean 4 formal proof gate (`--mode noproof`, 25 turns) and ask the exact same models to audit the Rust crates directly (`verdict.txt`: `safe` or `vulnerable`, plus `counterexample.json` and a patch if `vulnerable`), we measure **False Negatives (`FN`)** (vulnerable code certified `safe`) and **False Positives (`FP`)** (safe code claimed `vulnerable`):

| Security Audit Soundness Metric | With FV (`Lean 4`) — Opus 5.5 | With FV (`Lean 4`) — GPT 6.1 Sol | Without FV (`No-Proof`) — Opus 5.5 | Without FV (`No-Proof`) — GPT 6.1 Sol |
|---|---:|---:|---:|---:|
| **False Negatives (`FN`) — Multi-Module Crates (`zk-clearing`, `settlement-engine`)** | **`0.0%` (`0/2`)** | **`0.0%` (`0/2`)** | `0.0%` (`0/2`) | **`100.0%` (`2/2` certified `safe`)** |
| **False Negatives (`FN`) — Full Suite (`.vulnerable`)** | **`0.0%` (`0/10`)** | **`0.0%` (`0/10`)** | `0.0%` (`0/11`) | **`18.2%` (`2/11` certified `safe`)** |
| **False Positives (`FP`) — Full Suite (`.safe`)** | **`0.0%` (`0/10`)** | **`0.0%` (`0/10`)** | `0.0%` (`0/11`) | `0.0%` (`0/11`) |
| **Kernel-Verified Audit Certificates (`TP + TN`)** | **`90.0%` (`18/20`)** | **`75.0%` (`15/20`)** | **`0.0%` (`0/22`)** | **`0.0%` (`0/22`)** |
| **Safe Abstentions (`Unverified` / Blocked by Lean Kernel)** | `10.0%` (`2/20`) | `25.0%` (`5/20`) | `0.0%` (`0/22`, No Gate) | `0.0%` (`0/22`, No Gate) |

- **Mental Autocorrection (`settlement-engine-vulnerable`):** Without FV ([trajectory](evidence/v3-noproof/gpt-6.1-sol-high/gpt-6.1-sol-high-settlement-engine-vulnerable-noproof/gpt-6.1-sol-high-settlement-engi__XK9cbWP/agent/trajectory.json), Step 4), `GPT 6.1 Sol` transcribed `ceil_div_bps_u64` into Python (`/tmp/check.py`) by unconsciously copying the *fixed* formula from the neighboring `flash_loan` module, tested 209,261 inputs against its own corrected script, and certified the buggy crate `safe` (`FN`). With FV ([trajectory](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-settlement-engine-vulnerable/settlement-engine-vulnerable__GYayEHF/agent/trajectory.json)), `SecurityChallenge.lean` is mechanically extracted from the Rust AST, forcing the model to spot and fix the bug.
- **20M-Sample Differential Fuzzing Blindness (`zk-clearing-vulnerable`):** Without FV ([trajectory](evidence/v3-noproof/gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-vulnerable-noproof/gpt-6.1-sol-high-zk-clearing-vul__S6o5YTq/agent/trajectory.json), Step 20–22), `GPT 6.1 Sol` ran a 20,000,000-sample random 64-bit fuzzer (`examples/complete_check.rs`) plus a coarse boundary grid (`u64::MAX - 10_000, u64::MAX - 1`) that stepped right over the 3,383-wide pocket $[2^{64}-4999, 2^{64}-1617]$ ($p \approx 1.8 \times 10^{-16}$ per sample) and certified the buggy crate `safe` (`FN`). With FV ([trajectory](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-vulnerable/gpt-6.1-sol-high-zk-clearing-vul__jbSK3df/agent/trajectory.json)), proving `WordMath.lean` immediately exposed the defective branch, and when 25 turns expired before finishing the 10-module proof, the Lean kernel safely abstained (`0%` FN).
- **Per-task breakdown, token/turn metrics, and full `Proof` vs `No-Proof` audit classification:** [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md) · **Verifier architecture:** [BACKEND.md](BACKEND.md)

---

## Quick Start

```bash
# 1. Print the Formal Verification benchmark table or the FP/FN No-Proof ablation:
python3 scripts/summarize-results.py --all
python3 scripts/summarize-results.py --mode fp-fn --all

# 2. Generate the flagship zk-clearing Harbor task pairs (proof, noproof, or both):
python3 scripts/make-family.py /tmp/security-family --mode both

# 3. Run a Harbor evaluation on a generated task:
harbor run -p /tmp/security-family/zk-clearing-vulnerable \
  -a terminus-2 -m <model> \
  --ak reasoning_effort=high --ak max_turns=25 -e docker -n 1
```
