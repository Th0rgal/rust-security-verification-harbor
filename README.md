# Rust Security Verification Harbor

## Why This Benchmark?

Most security benchmarks either ask a model to guess whether a snippet has a bug, or hand the model a finished formal specification and ask it to fill in a proof.

This benchmark tests the **complete formal security workflow** on real-world Rust systems code. Every problem comes as a **symmetric pair (`-vulnerable` and `-safe`)** with the **exact same prompt** and passing unit tests—the model is never told whether the code is buggy or sound. Instead, we guide the model through three steps:

1. **Write the Specification (`Spec.lean` — `0.25`):** Formalize what the Rust code *should* compute in ideal, unbounded integer arithmetic (where machine overflow and bit-wrapping cannot happen).
2. **Audit the Implementation (`Audit.lean` + `Proof.lean` — `0.40`):** Compare the 64-bit machine implementation against that specification to determine whether it is **`.safe`** or **`.vulnerable`**, and prove that finding in Lean 4.31.
3. **Prove or Fix (`0.35`):**
   - **If `.safe`:** Prove in Lean 4.31 that the implementation matches the specification for **all** $2^{64} \times 2^{64} \times 2^{64}$ inputs.
   - **If `.vulnerable`:** Provide a concrete input that triggers the bug (`counterexample.json`), **patch the Rust code** (`src/lib.rs`), and pass a full-domain formal equivalence check proving the patched Rust code is universally correct.

Every step is **100% automatically verified** inside an isolated offline container (using the Lean 4.31 kernel checker `leanchecker` and Z3 over the full `u64` domain). Model text is never graded.

---

## The 6 Challenge Pairs (12 Harbor Tasks)

To apply the same verifier across different domains, each task wraps a real-world 64-bit Rust kernel into a unified `authorize(balance, amount, fee)` gate that authorizes an operation iff its target mathematical cost is $\le \text{balance}$.

By default (`python3 scripts/make-family.py /tmp/security-family`), the benchmark generates **6 non-redundant symmetric pairs (12 tasks)** spanning a clear difficulty gradient:

| Pair (`-vulnerable` / `-safe`) | Origin & Domain | Target Specification (What the code should compute) | The Bug in `.vulnerable` (Fixed in `.safe`) |
|---|---|---|---|
| **[`ruint`](problems/ruint)** | `alloy-rs/ruint` — Multiprecision Division | $\lfloor \text{amount}/2 \rfloor + \lfloor (((\text{fee} \bmod 32771) \cdot 2^{16} + (\text{amount} \bmod 2^{16})) / 32771 \rfloor$ | Möller-Granlund 2-by-1 reciprocal division (`div_2x1_mg10`) omits the second remainder correction `if r_corr >= D`, under-estimating the quotient by `1` on a narrow band of inputs. |
| **[`succinct`](problems/succinct)** | `tov/succinct-rs` — Non-Web3 SWAR Bitmaps | $\lfloor \text{amount}/2 \rfloor + (\text{sum of bytes of } \text{fee}) + 256 \times (\text{count of non-zero bytes of } \text{fee})$ | Vigna's broadword non-zero byte detector `(((x \| H8) - L8) \| x) & H8` omits `\| x`, silently treating every `0x80` (`128`) byte as zero. |
| **[`plonky3`](problems/plonky3)** | `Plonky3/Plonky3` — ZK BabyBear Field ($P = 2\,013\,265\,921$) | $\text{amount} + (((\text{amount} \bmod 2^{32}) + (\text{fee} \bmod P) \cdot 2^{32}) \cdot 943\,718\,400 \bmod P)$ | 64-bit Montgomery reduction adds `(1 << 32) - P` instead of `P` in the unsigned underflow branch after shifting by 32 bits. |
| **[`settlement-engine`](problems/settlement-engine)** | Multi-Module Settlement Engine (~330 lines Rust, 6 modules) | $\text{amount} + (\lceil (\text{amount}+\text{fee})/10\,000 \rceil - \lfloor \lceil (\text{amount}+\text{fee})/10\,000 \rceil / 10 \rfloor)$ | Pure-`u64` carry folding across 3 modules is exact at `u64::MAX`, but under-computes the fee by `1` inside a narrow high-sum pocket ($2^{64}-9\,999 \le \text{amount}+\text{fee} \le 2^{64}-1\,617$), surrounded by 6 sound helper functions acting as realistic noise. |
| **[`whirlpool`](problems/whirlpool)** | `orca-so/whirlpools` — DeFi 128-bit Ceiling Division | $\lfloor \text{amount}/2 \rfloor + \lceil (\text{amount} + \text{fee} \cdot 2^{64}) / 1\,000\,000 \rceil$ | 4-limb base-$2^{32}$ ceiling division drops the `w1 → w2` carry when rounding up `q0 = 2^32 - 1, q1 = 2^32 - 1` with non-zero remainder. |
| **[`goldilocks`](problems/goldilocks)** | `recmo/goldilocks` — ZK Goldilocks Field ($P = 2^{64}-2^{32}+1$) | $\lfloor \text{amount}/2 \rfloor + ((\text{amount} + \text{fee} \cdot 2^{64}) \bmod P)$ | 128-bit prime reduction checks `> P` instead of `>= P` in the final canonicalization step, leaving `r = P` unreduced. |

*(Note: Passing `--problem all` also generates 4 simpler calibration pairs—`authorization`, `settlement`, `settlement-modular`, and `openpql`—used in our regression suite `scripts/selftest.py`.)*

---

## Benchmark Results (`10` Turns Default vs. `25` Turns Extended)

We set the default benchmark budget to **10 turns (`max_turns=10`)**, which is a reasonable budget for an agent to specify, audit, and patch a task. We also ran an extended evaluation at **25 turns (`max_turns=25`)** to give models extra headroom and observe whether they can eventually close the hardest Lean 4 proofs:

- **Finding & patching bugs (`.vulnerable`) is fast:** Within **10 turns**, both **Claude Opus 5.5 (`high`)** and **GPT 6.1 Sol (`high`)** solve **6/6 `.vulnerable` tasks (`1.000`)**—formalizing the spec, proving the refutation, finding a counterexample, and patching the Rust code.
- **Proving universal safety (`.safe`) is the real differentiator:**
  - At **10 turns (default)**, **Claude Opus 5.5** closes **2/6** `.safe` proofs (**`0.688` overall**), while **GPT 6.1 Sol** closes **0/6** (**`0.625` overall**, earning only the `0.25` specification credit on `.safe` tasks).
  - At **25 turns (extended)**, **Claude Opus 5.5** closes **6/6** `.safe` proofs (**`1.000` overall**), whereas **GPT 6.1 Sol** closes **3/6** (**`0.813` overall**), failing on `ruint-safe`, `succinct-safe`, and `plonky3-safe`.

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

For full details on the verifier architecture and anti-cheating checks, see [BACKEND.md](BACKEND.md) and [evidence/v3/VALIDATION.md](evidence/v3/VALIDATION.md).
