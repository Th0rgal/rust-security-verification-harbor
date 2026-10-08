# Rust Security Verification Harbor

## Why This Approach Matters

Evaluating frontier models on formal security verification faces a fundamental dilemma:
- **If you hand the model a fixed theorem statement**, you have already done half the security auditor's job: the model immediately knows whether the code is safe or buggy, and never has to formalize the intended mathematical specification itself.
- **If you let the model write its own specification (`Spec.lean`) and prove it (`Proof.lean`)**, a naive Lean checker is trivially gamed: a model can write a vacuous specification (`False`), leave the output unconstrained, or copy the buggy fixed-width `u64` code into the specification and prove a 1-line tautology.

This benchmark solves both problems by pairing **symmetric blind tasks (`-vulnerable` and `-safe`, with byte-identical prompts)** and guiding the model through a **3-stage formal verification pipeline** that scales to complex, real-world Rust systems bugs:

1. **Formulate the Mathematical Specification (`Spec.lean`, weight `0.25`):**
   - The model defines in unbounded `Nat` arithmetic (where machine overflow cannot occur) when an operation should be accepted and what exact value it should produce.
   - **How we verify equivalence regardless of syntax:** The model can write `candidateSpec` using any combination of `let` bindings, helper functions, conditionals, shifts, masks, or Euclidean division. Inside the verifier container, a Lean 4.31 metaprogram (`SpecAudit.lean`) elaborates `Spec.lean`, unfolds definitions in the kernel environment, and extracts a normalized arithmetic AST. That AST is passed to `spec.py`, which applies **Euclidean quotient/remainder purification** (`a = d * q + r` with `0 <= r < d`, limb/byte decomposition, and interval bound propagation) to query **Z3 (`QF_NIA`) over the entire $2^{64} \times 2^{64} \times 2^{64}$ input space** across four independent facets (safety, completeness, output exactness/uniqueness, and non-vacuity). Any mathematically equivalent formulation gets full credit; vacuous or bug-copying specs fail with a concrete counterexample.

2. **Audit the Implementation and Prove the Verdict in Lean 4.31 (`Audit.lean` + `Proof.lean`, weight `0.40`):**
   - The model declares `verdict : AuditVerdict` (`.safe` or `.vulnerable`, weight `0.15`) and proves `AuditClaim candidateSpec verdict` (weight `0.25`) against the visible Lean model of the Rust implementation (`SecurityChallenge.lean`), verified by `leanchecker --fresh` with zero `sorry` or `bv_decide` / `native_decide` trust axioms.
   - **Why this works on hard problems:** Real arithmetic bugs hide in tiny corner cases (such as an 8,383-wide carry pocket near $2^{64}$, a single `0x80` byte in SWAR broadword logic, or a missing second remainder correction in reciprocal division) that unit tests and fuzzers miss. Attempting to prove a `.vulnerable` implementation `.safe` in Lean 4 immediately gets stuck on the exact failing subgoal, guiding the model to discover the bug and switch to a formal refutation.

3. **Resolve the Finding: Universal Safety or Verified Rust Patch (`counterexample.json` + `src/lib.rs`, weight `0.35`):**
   - **If `.safe`:** Closing the universal Lean 4.31 proof in Stage 2 certifies that the implementation matches `candidateSpec` across all `u64` inputs.
   - **If `.vulnerable`:** The model submits a concrete runtime counterexample (`counterexample.json`, `0.15`, checked against the compiled Rust binary) and a patched pure-`u64` Rust implementation (`src/lib.rs`, `0.20`), which is symbolically executed (`rust_symbolic.py`) and proven universally equivalent by Z3 over all `u64` inputs.

---

## Challenge Benchmark Suite & Results

By default (`python3 scripts/make-family.py /tmp/security-family`), the benchmark generates **6 non-redundant symmetric pairs (12 Harbor tasks)** spanning a clear difficulty gradient:
- **[`ruint`](problems/ruint)** (`alloy-rs/ruint` Möller-Granlund 2-by-1 reciprocal division)
- **[`succinct`](problems/succinct)** (`tov/succinct-rs` Vigna SWAR broadword byte detection)
- **[`plonky3`](problems/plonky3)** (`Plonky3/Plonky3` BabyBear 64-bit Montgomery reduction)
- **[`settlement-engine`](problems/settlement-engine)** (Multi-module financial engine with 6 red-herring calculators and an interior carry pocket)
- **[`whirlpool`](problems/whirlpool)** (`orca-so/whirlpools` 4-limb 128-bit ceiling division)
- **[`goldilocks`](problems/goldilocks)** (`recmo/goldilocks` 128-bit Goldilocks prime field reduction)

We evaluate models under a **10-turn default budget (`max_turns=10`)** and an **extended 25-turn budget (`max_turns=25`)**:

| Summary (12 Challenge Tasks) | Claude Opus 5.5 (`high`) @ **10T** | Claude Opus 5.5 (`high`) @ **25T** | GPT 6.1 Sol (`high`) @ **10T** | GPT 6.1 Sol (`high`) @ **25T** |
|---|---:|---:|---:|---:|
| **`.vulnerable` tasks (`6` tasks)** | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) |
| **`.safe` tasks (`6` tasks)** | **0.375** (`2.25 / 6`) | **1.000** (`6.00 / 6`) | **0.250** (`1.50 / 6`) | **0.625** (`3.75 / 6`) |
| **Overall Mean (`12` tasks)** | **0.688** (`8.25 / 12`) | **1.000** (`12.00 / 12`) | **0.625** (`7.50 / 12`) | **0.813** (`9.75 / 12`) |

- **Full specification formulas, per-task token/turn breakdown, and proof/failure trace links:** see **[evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md)** (or run `python3 scripts/summarize-results.py`).
- **Verifier architecture and AST lowering details:** see **[BACKEND.md](BACKEND.md)**.

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
