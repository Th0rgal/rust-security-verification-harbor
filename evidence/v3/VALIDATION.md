# Benchmark Details & Per-Task Breakdown (v3)

## 1. The 6 Challenge Pairs (12 Harbor Tasks)

Each problem wraps a real-world 64-bit Rust arithmetic kernel into a unified `authorize(balance, amount, fee) -> Option<Authorization>` gate that authorizes an operation iff its target mathematical cost is $\le \text{balance}$.

| Pair (`-vulnerable` / `-safe`) | Origin & Domain | Target Specification (Unbounded `Nat`) | Bug in `.vulnerable` (Fixed in `.safe`) |
|---|---|---|---|
| **[`ruint`](../../problems/ruint)** | `alloy-rs/ruint` (Multiprecision Division) | $\lfloor \text{amount}/2 \rfloor + \lfloor (((\text{fee} \bmod 32771) \cdot 2^{16} + (\text{amount} \bmod 2^{16})) / 32771 \rfloor$ | Möller-Granlund 2-by-1 reciprocal division (`div_2x1_mg10`, `D = 0x8003`, `V = 0xFFF4`) omits the second conditional remainder correction `if r_corr >= D`, under-estimating the quotient by `1` when `r_corr` falls in `[D, 2D)`. |
| **[`succinct`](../../problems/succinct)** | `tov/succinct-rs` (Non-Web3 SWAR Bitmaps) | $\lfloor \text{amount}/2 \rfloor + (\text{sum of bytes of } \text{fee}) + 256 \times (\text{count of non-zero bytes of } \text{fee})$ | Vigna's SWAR broadword non-zero byte detector `(((x \| H8) - L8) \| x) & H8` omits `\| x`, silently treating every byte equal to `0x80` (`128`) as zero. |
| **[`plonky3`](../../problems/plonky3)** | `Plonky3/Plonky3` (ZK BabyBear Field, $P = 2\,013\,265\,921$) | $\text{amount} + (((\text{amount} \bmod 2^{32}) + (\text{fee} \bmod P) \cdot 2^{32}) \cdot 943\,718\,400 \bmod P)$ | 64-bit Montgomery reduction (`MU = 2_281_701_377`) adds `(1 << 32) - P` instead of `P` in the unsigned underflow branch after shifting by 32 bits. |
| **[`settlement-engine`](../../problems/settlement-engine)** | Multi-Module Settlement Engine (~330 lines Rust, 6 modules) | $\text{amount} + (\lceil (\text{amount}+\text{fee})/10\,000 \rceil - \lfloor \lceil (\text{amount}+\text{fee})/10\,000 \rceil / 10 \rfloor)$ | Pure-`u64` carry folding across 3 modules is exact at `u64::MAX`, but under-computes the fee by `1` inside an interior pocket ($2^{64}-9\,999 \le \text{amount}+\text{fee} \le 2^{64}-1\,617$), surrounded by 6 sound sibling calculators acting as realistic noise. |
| **[`whirlpool`](../../problems/whirlpool)** | `orca-so/whirlpools` (DeFi 128-bit Ceiling Division) | $\lfloor \text{amount}/2 \rfloor + \lceil (\text{amount} + \text{fee} \cdot 2^{64}) / 1\,000\,000 \rceil$ | 4-limb base-$2^{32}$ ceiling division drops the `w1 -> w2` carry when rounding up `q0 = 2^32 - 1, q1 = 2^32 - 1` with non-zero remainder, wrapping a $2^{64}$ quotient to `0`. |
| **[`goldilocks`](../../problems/goldilocks)** | `recmo/goldilocks` (ZK Goldilocks Field, $P = 2^{64}-2^{32}+1$) | $\lfloor \text{amount}/2 \rfloor + ((\text{amount} + \text{fee} \cdot 2^{64}) \bmod P)$ | Two-step 128-bit Goldilocks reduction checks `> P` instead of `>= P` in the final canonicalization step, leaving a single unreduced residue `r = P`. |

*(Passing `--problem all` to `scripts/make-family.py` also generates 4 auxiliary calibration pairs: `authorization`, `settlement`, `settlement-modular`, and `openpql`.)*

---

## 2. Per-Task Breakdown (`10` Turns Default vs. `25` Turns Extended)

Reproducible via `python3 scripts/summarize-results.py` (or `python3 scripts/summarize-results.py --all`):

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
| **Mean (12 tasks)** | **All** | **0.688** (`8.25/12`) | **1.000** (`12.00/12`) | - | - | **0.625** (`7.50/12`) | **0.813** (`9.75/12`) | - | - |

### Direct Proof & Failure Inspection Links

- **`ruint-safe`:** [Reference Proof](../../problems/ruint/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 23T) Report](claude-opus-5-5/claude-opus-5-5-ruint-safe/ruint-safe__kP8qzNh/verifier/details.json) & [Transcript](claude-opus-5-5/claude-opus-5-5-ruint-safe/ruint-safe__kP8qzNh/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, failed `omega`) Report](gpt-6.1-sol-high/gpt-6.1-sol-high-ruint-safe/ruint-safe__HcwaH48/verifier/details.json) & [Transcript](gpt-6.1-sol-high/gpt-6.1-sol-high-ruint-safe/ruint-safe__HcwaH48/agent/terminus_2.pane)
- **`succinct-safe`:** [Reference Proof](../../problems/succinct/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 15T) Report](claude-opus-5-5/claude-opus-5-5-succinct-safe/succinct-safe__vSngWU9/verifier/details.json) & [Transcript](claude-opus-5-5/claude-opus-5-5-succinct-safe/succinct-safe__vSngWU9/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, disallowed `bv_decide`) Report](gpt-6.1-sol-high/gpt-6.1-sol-high-succinct-safe/succinct-safe__oYsCe2P/verifier/details.json) & [Transcript](gpt-6.1-sol-high/gpt-6.1-sol-high-succinct-safe/succinct-safe__oYsCe2P/agent/terminus_2.pane)
- **`plonky3-safe`:** [Reference Proof](../../problems/plonky3/solution/safe/Proof.lean) · [Opus 5.5 (`1.00`, 16T) Report](claude-opus-5-5/claude-opus-5-5-plonky3-safe/plonky3-safe__ByhaTT4/verifier/details.json) & [Transcript](claude-opus-5-5/claude-opus-5-5-plonky3-safe/plonky3-safe__ByhaTT4/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.25`, left `sorry`) Report](gpt-6.1-sol-high/gpt-6.1-sol-high-plonky3-safe/plonky3-safe__K6xkgTV/verifier/details.json) & [Transcript](gpt-6.1-sol-high/gpt-6.1-sol-high-plonky3-safe/plonky3-safe__K6xkgTV/agent/terminus_2.pane)

---

## 3. Verifier Validation & Adversarial Regression (`scripts/selftest.py`)

All 20 reference solutions (`1.00`) and skeletons (`0.00`), plus adversarial test cases (vacuous specs, under-constrained outputs, `sorry` / `bv_decide` / `native_decide` axiom injection, invalid counterexamples, non-equivalent Rust patches, symlink escapes), are verified offline via:

```bash
docker build -t security-verifier:v3 -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3 python3 /repo/scripts/selftest.py
```

The final output is `selftest v3: PASS`, with reference receipts recorded in `evidence/v3/*-reference.json`.
