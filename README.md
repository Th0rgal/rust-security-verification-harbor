# Rust Security Verification Harbor

## Why This Approach Matters

Evaluating frontier models on formal security verification faces a fundamental dilemma:
- **If you hand the model a fixed theorem statement**, you have already done half the security auditor's job: the model immediately knows whether the code is safe or buggy, and does not have to formalize the intended mathematical specification itself.
- **If you let the model write its own specification (`Spec.lean`) and prove it (`Proof.lean`)**, a naive Lean checker is trivially gamed: a model can write a vacuous specification (`False`), leave the output unconstrained, or copy the buggy fixed-width `u64` code into the specification and prove a 1-line tautology.

This benchmark solves both problems by combining **symmetric blind task pairs** with a **two-layer formal verification architecture (Lean 4.31 kernel replay + full-domain Z3 semantic equivalence)** that scales to complex, real-world Rust arithmetic kernels.

### How the Architecture Works

Every problem is packaged as two separate Harbor tasks (`-vulnerable` and `-safe`) with **byte-identical instructions** and passing unit tests. For each task, the model must complete three coupled stages inside an offline container:

1. **Formulate the Mathematical Specification (`Spec.lean`, weight `0.25`):**
   - The model writes `candidateSpec : AuthorizationSpec`, defining in unbounded natural-number arithmetic (`Nat`, where machine overflow cannot occur) when an operation should be accepted and what exact value it should produce.
   - **How we verify equivalence regardless of how the model writes the spec:** The model is free to express `candidateSpec` using any combination of `let` bindings, helper functions, conditionals, shifts, masks, or modular arithmetic. Inside the verifier container, a Lean 4.31 metaprogram (`SpecAudit.lean`) elaborates `Spec.lean`, unfolds definitions in the kernel environment, and extracts a normalized arithmetic AST. That AST is passed to `spec.py`, which applies **Euclidean quotient/remainder purification** (`a = d * q + r` with `0 <= r < d`, limb/byte decomposition, and interval bound propagation) to query **Z3 (`QF_NIA`) over the entire $2^{64} \times 2^{64} \times 2^{64}$ input space** across four independent facets:
     1. *Safety* (`accepts -> target_cost <= balance`),
     2. *Completeness* (`target_cost <= balance -> accepts`),
     3. *Output exactness & uniqueness* (`accepts /\ output -> total = target_cost`),
     4. *Non-vacuity & output existence* (rejects empty or contradictory specs).
   - Because Z3 proves semantic equivalence over all `u64` inputs, any mathematically equivalent formulation gets full credit, while vacuous, under-constrained, or bug-copying specs fail with a concrete counterexample.

2. **Audit the Implementation and Prove the Verdict in Lean 4.31 (`Audit.lean` + `Proof.lean`, weight `0.40`):**
   - The model declares `verdict : AuditVerdict` (`.safe` or `.vulnerable`, weight `0.15`) and proves `AuditClaim candidateSpec verdict` (weight `0.25`) against the visible Lean model of the Rust implementation (`SecurityChallenge.lean`).
   - **Why this works for hard bugs:** Production arithmetic bugs often hide in minuscule corner cases (such as an 8,383-wide carry pocket near $2^{64}$, a single `0x80` byte in SWAR broadword logic, or a missing second remainder correction in reciprocal division) that pass standard tests and random fuzzing. Trying to prove a `.vulnerable` implementation `.safe` in Lean 4 immediately gets stuck on the exact failing subgoal, guiding the model to discover the bug and switch to a refutation proof.
   - **Kernel-level anti-cheating:** `Proof.lean` is compiled in a Landlock + seccomp sandbox (`uid 65534`), replayed from scratch by `leanchecker --fresh`, and audited with `loadExts := false`. Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are permitted (`sorry`, custom `axiom`, `native_decide`, and `bv_decide` trust axioms are rejected). On `.safe` tasks, verdict credit is gated on a valid proof so guessing `.safe` scores `0.00`.

3. **Resolve the Finding: Universal Safety or Verified Rust Patch (`counterexample.json` + `src/lib.rs`, weight `0.35`):**
   - **If `.safe`:** Closing the universal Lean 4.31 proof in Stage 2 certifies that the implementation matches `candidateSpec` across all $2^{64} \times 2^{64} \times 2^{64}$ inputs (and no witness or patch files may be submitted).
   - **If `.vulnerable`:** The model must submit:
     - `counterexample.json` (`0.15`): a concrete `(balance, amount, fee)` input verified against the pristine compiled Rust binary (`rustc -O`) to demonstrate a real runtime violation.
     - `src/lib.rs` (`0.20`): a patched pure-`u64` Rust implementation (`u128` is disallowed in extended problems). Our symbolic Rust executor (`rust_symbolic.py`) parses the patched Rust AST, symbolically executes all control-flow paths, and uses Z3 purification to prove universal equivalence of the patched Rust code over all `u64` inputs, backed by compiled `rustc -O` regression tests.

---

## The 6 Challenge Pairs (12 Harbor Tasks)

To apply this unified verification pipeline across diverse domains, each problem wraps a real-world 64-bit Rust arithmetic kernel into a common `authorize(balance, amount, fee) -> Option<Authorization>` entry point that authorizes an operation iff its target mathematical cost is $\le \text{balance}$.

By default (`python3 scripts/make-family.py /tmp/security-family`), the generator emits **6 non-redundant symmetric pairs (12 Harbor tasks)** spanning a broad gradient of domain and proof complexity:

| Pair (`-vulnerable` / `-safe`) | Origin & Domain | Target Specification (Unbounded `Nat`) | Bug in `.vulnerable` (Fixed in `.safe`) |
|---|---|---|---|
| **[`ruint`](problems/ruint)** | `alloy-rs/ruint` (Multiprecision Division) | $\lfloor \text{amount}/2 \rfloor + \lfloor (((\text{fee} \bmod 32771) \cdot 2^{16} + (\text{amount} \bmod 2^{16})) / 32771 \rfloor$ | Möller-Granlund 2-by-1 reciprocal division (`div_2x1_mg10`, `D = 0x8003`, `V = 0xFFF4`) omits the second conditional remainder correction `if r_corr >= D`, under-estimating the quotient by `1` when `r_corr` falls in `[D, 2D)`. |
| **[`succinct`](problems/succinct)** | `tov/succinct-rs` (Non-Web3 SWAR Bitmaps) | $\lfloor \text{amount}/2 \rfloor + (\text{sum of bytes of } \text{fee}) + 256 \times (\text{count of non-zero bytes of } \text{fee})$ | Vigna's SWAR broadword non-zero byte detector `(((x \| H8) - L8) \| x) & H8` omits `\| x`, silently treating every byte equal to `0x80` (`128`) as zero. |
| **[`plonky3`](problems/plonky3)** | `Plonky3/Plonky3` (ZK BabyBear Field, $P = 2\,013\,265\,921$) | $\text{amount} + (((\text{amount} \bmod 2^{32}) + (\text{fee} \bmod P) \cdot 2^{32}) \cdot 943\,718\,400 \bmod P)$ | 64-bit Montgomery reduction (`MU = 2_281_701_377`) adds `(1 << 32) - P` instead of `P` in the unsigned underflow branch after shifting by 32 bits. |
| **[`settlement-engine`](problems/settlement-engine)** | Multi-Module Settlement Engine (~330 lines Rust, 6 modules) | $\text{amount} + (\lceil (\text{amount}+\text{fee})/10\,000 \rceil - \lfloor \lceil (\text{amount}+\text{fee})/10\,000 \rceil / 10 \rfloor)$ | Pure-`u64` carry folding across 3 modules is exact at `u64::MAX`, but under-computes the fee by `1` inside an interior pocket ($2^{64}-9\,999 \le \text{amount}+\text{fee} \le 2^{64}-1\,617$), surrounded by 6 sound sibling calculators acting as realistic noise. |
| **[`whirlpool`](problems/whirlpool)** | `orca-so/whirlpools` (DeFi 128-bit Ceiling Division) | $\lfloor \text{amount}/2 \rfloor + \lceil (\text{amount} + \text{fee} \cdot 2^{64}) / 1\,000\,000 \rceil$ | 4-limb base-$2^{32}$ ceiling division drops the `w1 -> w2` carry when rounding up `q0 = 2^32 - 1, q1 = 2^32 - 1` with non-zero remainder, wrapping a $2^{64}$ quotient to `0`. |
| **[`goldilocks`](problems/goldilocks)** | `recmo/goldilocks` (ZK Goldilocks Field, $P = 2^{64}-2^{32}+1$) | $\lfloor \text{amount}/2 \rfloor + ((\text{amount} + \text{fee} \cdot 2^{64}) \bmod P)$ | Two-step 128-bit Goldilocks reduction checks `> P` instead of `>= P` in the final canonicalization step, leaving a single unreduced residue `r = P`. |

*(Passing `--problem all` also generates 4 auxiliary calibration pairs (`authorization`, `settlement`, `settlement-modular`, and `openpql`) used in the full 20-variant regression suite `scripts/selftest.py`.)*

---

## Benchmark Results (`10` Turns Default vs. `25` Turns Extended)

We set the default benchmark horizon to **10 turns (`max_turns=10`)**, which is a practical budget for an agent to specify, audit, and patch a task. To measure each model's asymptotic formal-proof capability without turn truncation, we also ran an extended evaluation at **25 turns (`max_turns=25`)**:

- **Refuting and patching `.vulnerable` tasks (`6/6` solved within 10 turns):** Both **Claude Opus 5.5 (`high`)** and **GPT 6.1 Sol (`high`)** achieve **`1.000`** across all 6 `.vulnerable` tasks within 10 turns (formalizing `Spec.lean`, proving the refutation in `Proof.lean`, extracting `counterexample.json`, and writing a Z3-verified Rust patch in `src/lib.rs`).
- **Proving universal safety on `.safe` tasks (the core differentiator):**
  - At **10 turns (default)**, **Claude Opus 5.5** closes **2/6** universal `.safe` proofs (**`0.688` overall**), while **GPT 6.1 Sol** closes **0/6** (**`0.625` overall**, earning only the `0.25` specification credit on `.safe` tasks).
  - At **25 turns (extended)**, **Claude Opus 5.5** closes **6/6** universal `.safe` proofs (**`1.000` overall**), whereas **GPT 6.1 Sol** closes **3/6** (**`0.813` overall**), failing at `0.25` on the three hardest non-linear/bitwise proofs (`ruint-safe`, `succinct-safe`, and `plonky3-safe`).

| Summary (12 Challenge Tasks) | Claude Opus 5.5 (`high`) @ **10T** | Claude Opus 5.5 (`high`) @ **25T** | GPT 6.1 Sol (`high`) @ **10T** | GPT 6.1 Sol (`high`) @ **25T** |
|---|---:|---:|---:|---:|
| **`.vulnerable` tasks (`6` tasks)** | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) | **1.000** (`6.00 / 6`) |
| **`.safe` tasks (`6` tasks)** | **0.375** (`2.25 / 6`) | **1.000** (`6.00 / 6`) | **0.250** (`1.50 / 6`) | **0.625** (`3.75 / 6`) |
| **Overall Mean (`12` tasks)** | **0.688** (`8.25 / 12`) | **1.000** (`12.00 / 12`) | **0.625** (`7.50 / 12`) | **0.813** (`9.75 / 12`) |

### Per-Task Breakdown

| Task | Variant | Opus 5.5 @ **10T** | Opus 5.5 @ **25T** | Opus 5.5 Turns | Opus 5.5 Tokens (`in` + `out`) | GPT 6.1 Sol @ **10T** | GPT 6.1 Sol @ **25T** | GPT 6.1 Sol Turns | GPT 6.1 Sol Tokens (`in` + `out`) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `ruint-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 9 | 107.3k (95.8k + 11.5k) | **1.00** | **1.00** | 10 | 84.2k (80.6k + 3.6k) |
| `ruint-safe` | `.safe` | **0.00** | **1.00** | 23 | 665.6k (606.7k + 58.9k) | **0.25** | **0.25 ❌** | 25 | 671.7k (661.5k + 10.2k) |
| `succinct-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 9 | 116.7k (106.5k + 10.2k) | **1.00** | **1.00** | 7 | 58.5k (54.8k + 3.6k) |
| `succinct-safe` | `.safe` | **0.00** | **1.00** | 15 | 572.9k (519.2k + 53.7k) | **0.25** | **0.25 ❌** | 25 | 745.1k (735.4k + 9.7k) |
| `plonky3-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 91.4k (78.4k + 13.0k) | **1.00** | **1.00** | 10 | 83.1k (79.0k + 4.2k) |
| `plonky3-safe` | `.safe` | **0.00** | **1.00** | 16 | 490.2k (427.5k + 62.7k) | **0.25** | **0.25 ❌** | 25 | 537.2k (528.5k + 8.7k) |
| `settlement-engine-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 12 *(done T8)* | 218.3k (203.6k + 14.7k) | **1.00** | **1.00** | 12 *(done T9)* | 146.3k (142.0k + 4.4k) |
| `settlement-engine-safe` | `.safe` | **0.25** | **1.00** | 20 | 354.7k (326.2k + 28.5k) | **0.25** | **1.00** | 25 | 582.2k (574.3k + 8.0k) |
| `whirlpool-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 90.8k (79.6k + 11.2k) | **1.00** | **1.00** | 10 | 92.6k (88.3k + 4.3k) |
| `whirlpool-safe` | `.safe` | **1.00** | **1.00** | 11 *(done T9)* | 260.1k (207.8k + 52.3k) | **0.25** | **1.00** | 21 | 573.1k (562.7k + 10.5k) |
| `goldilocks-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 91.4k (79.5k + 12.0k) | **1.00** | **1.00** | 9 | 73.7k (69.6k + 4.0k) |
| `goldilocks-safe` | `.safe` | **1.00** | **1.00** | 10 | 374.9k (318.9k + 56.0k) | **0.25** | **1.00** | 25 | 530.0k (520.2k + 9.8k) |

### Inspecting the 3 Hardest `.safe` Proofs (`Opus 5.5` vs. `GPT 6.1 Sol`)

- **`ruint-safe`:** [Reference Proof](problems/ruint/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 23T) Report](evidence/v3/claude-opus-5-5/claude-opus-5-5-ruint-safe/ruint-safe__kP8qzNh/verifier/details.json) & [Transcript](evidence/v3/claude-opus-5-5/claude-opus-5-5-ruint-safe/ruint-safe__kP8qzNh/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, failed `omega`) Report](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-ruint-safe/ruint-safe__HcwaH48/verifier/details.json) & [Transcript](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-ruint-safe/ruint-safe__HcwaH48/agent/terminus_2.pane)
- **`succinct-safe`:** [Reference Proof](problems/succinct/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 15T) Report](evidence/v3/claude-opus-5-5/claude-opus-5-5-succinct-safe/succinct-safe__vSngWU9/verifier/details.json) & [Transcript](evidence/v3/claude-opus-5-5/claude-opus-5-5-succinct-safe/succinct-safe__vSngWU9/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, disallowed `bv_decide`) Report](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-succinct-safe/succinct-safe__oYsCe2P/verifier/details.json) & [Transcript](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-succinct-safe/succinct-safe__oYsCe2P/agent/terminus_2.pane)
- **`plonky3-safe`:** [Reference Proof](problems/plonky3/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 16T) Report](evidence/v3/claude-opus-5-5/claude-opus-5-5-plonky3-safe/plonky3-safe__ByhaTT4/verifier/details.json) & [Transcript](evidence/v3/claude-opus-5-5/claude-opus-5-5-plonky3-safe/plonky3-safe__ByhaTT4/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, left `sorry`) Report](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-plonky3-safe/plonky3-safe__K6xkgTV/verifier/details.json) & [Transcript](evidence/v3/gpt-6.1-sol-high/gpt-6.1-sol-high-plonky3-safe/plonky3-safe__K6xkgTV/agent/terminus_2.pane)

---

## Quick Start

```bash
# 1. Print the @10T vs @25T benchmark summary table from the committed Harbor traces:
python3 scripts/summarize-results.py

# 2. Generate the 12 Harbor tasks (6 Challenge pairs) into /tmp/security-family:
python3 scripts/make-family.py /tmp/security-family

# 3. Run a 10-turn Harbor evaluation on any generated task:
harbor run -p /tmp/security-family/ruint-safe \
  -a terminus-2 -m <model> \
  --ak reasoning_effort=high --ak max_turns=10 -e docker -n 1

# 4. Run the offline verifier self-test across all 20 variants (ends with "selftest v3: PASS"):
docker build -t security-verifier:v3 -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3 python3 /repo/scripts/selftest.py
```

For full details on the verifier implementation, AST lowering, and anti-cheating checks, see [BACKEND.md](BACKEND.md) and [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md).
