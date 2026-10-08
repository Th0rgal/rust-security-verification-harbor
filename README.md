# Rust Security Verification Harbor

Each task in this benchmark gives an agent a real-world 64-bit Rust arithmetic kernel without telling it whether the code is safe or buggy. Every problem exists as two Harbor tasks (`-vulnerable` and `-safe`) with the exact same prompt and passing unit tests.

Instead of giving the model a pre-written theorem statement (which leaks the answer), we ask the model to write its own formal specification and proof, and we grade the submission automatically in three steps:

1. **Specification (`Spec.lean`, `0.25`):**
   The model formalizes what the Rust function should compute in unbounded `Nat` arithmetic (where machine overflow cannot happen). Because the model writes `Spec.lean` itself, a naive Lean checker could be gamed by a vacuous spec (`False`) or by copying the buggy `u64` code into the spec. To prevent this while accepting any valid mathematical formulation, our Lean 4.31 metaprogram (`SpecAudit.lean`) unfolds the submitted spec into a normalized arithmetic AST, and `spec.py` uses Z3 (`QF_NIA` with Euclidean quotient/remainder purification) to verify semantic equivalence over all $2^{64} \times 2^{64} \times 2^{64}$ inputs across four facets (safety, completeness, output exactness, and non-vacuity).

2. **Audit & Lean 4.31 Proof (`Audit.lean` + `Proof.lean`, `0.40`):**
   The model declares `.safe` or `.vulnerable` (`0.15`) and proves `AuditClaim candidateSpec verdict` (`0.25`) against the visible Lean model of the Rust code (`SecurityChallenge.lean`), checked from scratch by `leanchecker --fresh` (no `sorry`, custom `axiom`, `native_decide`, or `bv_decide`). On `.vulnerable` tasks, the bugs sit in narrow arithmetic corner cases that unit tests and fuzzers miss; attempting a `.safe` proof fails on the exact broken subgoal and guides the model to a formal refutation.

3. **Resolution (`counterexample.json` + `src/lib.rs`, `0.35`):**
   - **If `.safe`:** The universal Lean 4.31 proof in Step 2 completes the task.
   - **If `.vulnerable`:** The model provides a concrete input (`counterexample.json`, `0.15`) that breaks the compiled Rust binary (`rustc -O`), and a patched pure-`u64` Rust implementation (`src/lib.rs`, `0.20`) that our symbolic executor (`rust_symbolic.py`) verifies in Z3 over all `u64` inputs.

---

## Challenge Benchmark Suite & Results

By default (`python3 scripts/make-family.py /tmp/security-family`), the benchmark generates **6 non-redundant symmetric pairs (12 Harbor tasks)**:
- **[`ruint`](problems/ruint)**: `alloy-rs/ruint` Möller-Granlund 2-by-1 reciprocal division
- **[`succinct`](problems/succinct)**: `tov/succinct-rs` Vigna SWAR broadword byte detection
- **[`plonky3`](problems/plonky3)**: `Plonky3/Plonky3` BabyBear 64-bit Montgomery reduction
- **[`settlement-engine`](problems/settlement-engine)**: Multi-module financial engine with 6 red-herring calculators and an interior carry pocket
- **[`whirlpool`](problems/whirlpool)**: `orca-so/whirlpools` 4-limb 128-bit ceiling division
- **[`goldilocks`](problems/goldilocks)**: `recmo/goldilocks` 128-bit Goldilocks prime field reduction

We evaluate models under a **10-turn default budget (`max_turns=10`)** and an **extended 25-turn budget (`max_turns=25`)**:

| Summary (12 Challenge Tasks) | Claude Opus 5.5 (`high`) @ **10T** | Claude Opus 5.5 (`high`) @ **25T** | GPT 6.1 Sol (`high`) @ **10T** | GPT 6.1 Sol (`high`) @ **25T** |
|---|---:|---:|---:|---:|
| **`.vulnerable` tasks (`6` tasks)** | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) |
| **`.safe` tasks (`6` tasks)** | **0.375** (`2.25 / 6`) | **1.000** (`6.00 / 6`) | **0.250** (`1.50 / 6`) | **0.625** (`3.75 / 6`) |
| **Overall Mean (`12` tasks)** | **0.688** (`8.25 / 12`) | **1.000** (`12.00 / 12`) | **0.625** (`7.50 / 12`) | **0.813** (`9.75 / 12`) |

- **Specification formulas, per-task token/turn breakdown, and proof/failure trace links:** [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md)
- **Verifier architecture and AST lowering details:** [BACKEND.md](BACKEND.md)

---

## Quick Start

```bash
# 1. Print the @10T vs @25T per-task table from the committed Harbor traces:
python3 scripts/summarize-results.py

# 2. Generate the 12 Harbor tasks (6 Challenge pairs) into /tmp/security-family:
python3 scripts/make-family.py /tmp/security-family

# 3. Run a 10-turn Harbor evaluation on any generated task:
harbor run -p /tmp/security-family/ruint-safe \
  -a terminus-2 -m <model> \
  --ak reasoning_effort=high --ak max_turns=10 -e docker -n 1
```
