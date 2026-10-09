# Benchmark Details & Per-Task Breakdown (v3)

## 1. Flagship Multi-Module Benchmark (`zk-clearing`)

The default benchmark (`python3 scripts/make-family.py /tmp/security-family`) generates the symmetric pair **`zk-clearing-vulnerable`** and **`zk-clearing-safe`** from [`problems/zk-clearing`](../../problems/zk-clearing).

### Crate & Lean Model Structure
- **Rust Crate (`1,540` LOC across `11` files in `src/`, `37` unit tests):**
  - [`src/lib.rs`](../../problems/zk-clearing/safe/src/lib.rs): Public `authorize(balance, amount, fee) -> Option<Authorization>` entrypoint and crate-level protocol contract (no closed-form formula cheat-sheet; agents must trace all 10 modules).
  - [`src/constants.rs`](../../problems/zk-clearing/safe/src/constants.rs): Protocol basis-point, flash-loan, reciprocal division, SWAR bitmask, BabyBear Montgomery, Goldilocks, and transcript framing constants.
  - [`src/word_math.rs`](../../problems/zk-clearing/safe/src/word_math.rs): 64-bit carry/borrow word arithmetic (`WordSum`, `WordDiff`) and pure-`u64` carry-folded floor/ceiling division by `10_000` (`BPS_DENOM`) and `5_000` (`FLASH_DENOM`).
  - [`src/fee_schedule.rs`](../../problems/zk-clearing/safe/src/fee_schedule.rs): Basis-point settlement fee calculator with 10% floor tier rebate (`gross_fee - gross_fee / 10`), passive floor fee, and tier classification.
  - [`src/liquidity_pool.rs`](../../problems/zk-clearing/safe/src/liquidity_pool.rs): Flash-settlement LP reserve retention (`flash_levy - flash_levy / 4` where `flash_levy = ceil((amount + fee) / 5000)`), flash-loan repayment receipts, and solvency checks.
  - [`src/reciprocal_div.rs`](../../problems/zk-clearing/safe/src/reciprocal_div.rs): Möller-Granlund (`alloy-rs/ruint` algorithm `MG10`) 2-by-1 normalized reciprocal division (`D = 32771`, `V = 0xFFF4`) for L1 blob gas slot pricing.
  - [`src/broadword_swar.rs`](../../problems/zk-clearing/safe/src/broadword_swar.rs): Vigna (`tov/succinct-rs`) 8-lane SWAR broadword non-zero byte detection (`u_nz8`, `count_nz_bytes`) and parallel byte-weight accumulation (`sum_bytes`).
  - [`src/montgomery_field.rs`](../../problems/zk-clearing/safe/src/montgomery_field.rs): `Plonky3` BabyBear ($P_{\text{BB}} = 2\,013\,265\,921$, $\mu = 2\,281\,701\,377$) 32-bit Montgomery reduction (`monty_reduce`) for STARK transcript verification levies.
  - [`src/transcript_codec.rs`](../../problems/zk-clearing/safe/src/transcript_codec.rs): Sequencer transcript domain tag decoding (`fee & 0xFF`, defaulting to `SEQUENCER_DOMAIN_TAG = 0x5A = 90` when `0`), header framing, and digest mixing.
  - [`src/goldilocks_field.rs`](../../problems/zk-clearing/safe/src/goldilocks_field.rs): `recmo/goldilocks` ($P_{\text{GL}} = 2^{64} - 2^{32} + 1$, $\epsilon = 2^{32} - 1$) two-step 128-bit field reduction (`reduce_goldilocks_128`) and canonical bridge verifier fee quoting.
  - [`src/clearing_pipeline.rs`](../../problems/zk-clearing/safe/src/clearing_pipeline.rs): Multi-stage clearing orchestrator combining all 6 active surcharge stages across all 10 modules into `ClearingBreakdown` (`base_surcharge` + `bridge_surcharge`) and `ClearingTicket` (`base_surcharge.checked_add(bridge_surcharge)` then `amount.checked_add(total_surcharge)`).
- **Lean 4.31 Functional Model (`676` LOC across `10` modules in `LeanModel/` + `SecurityChallenge.lean`, `1,046` LOC in `Proof.lean`):**
  Mirrors all 10 Rust modules in fixed-width `UInt64` arithmetic (`LeanModel/Constants.lean`, `WordMath.lean`, `ReciprocalDiv.lean`, `BroadwordSwar.lean`, `MontgomeryField.lean`, `GoldilocksField.lean`, `FeeSchedule.lean`, `LiquidityPool.lean`, `TranscriptCodec.lean`, `ClearingPipeline.lean`).

### Target Unbounded `Nat` Specification
For inputs `(balance, amount, fee)` with $b = \text{balance.toNat}$, $a = \text{amount.toNat}$, $f = \text{fee.toNat}$:
$$\text{totalDebit}(a, f) = a + \left(\lceil (a + f)/10\,000 \rceil - \lfloor \lceil (a + f)/10\,000 \rceil / 10 \rfloor\right) + \left(\lceil (a + f)/5\,000 \rceil - \lfloor \lceil (a + f)/5\,000 \rceil / 4 \rfloor\right) + \left\lfloor \frac{(f \bmod 32\,771) \cdot 2^{16} + (a \bmod 2^{16})}{32\,771} \right\rfloor + \sum_{i=0}^{7} \left(256 \cdot \mathbf{1}_{b_i(f) > 0} + b_i(f)\right) + \left(\left((a \bmod 2^{32}) + (f \bmod P_{\text{BB}}) \cdot 2^{32}\right) \cdot 943\,718\,400 \bmod P_{\text{BB}}\right) + \text{ite}(b_0(f) = 0, 90, b_0(f)) + \left((a + f \cdot 2^{64}) \bmod P_{\text{GL}}\right)$$
where $b_i(f) = \lfloor f / 2^{8i} \rfloor \bmod 256$, $P_{\text{BB}} = 2\,013\,265\,921$, and $P_{\text{GL}} = 18\,446\,744\,069\,414\,584\,321$. The gate authorizes iff $\text{totalDebit}(a, f) \le b$.

### Vulnerability & Cross-Module Coupling in `zk-clearing-vulnerable`
In `src/word_math.rs` (`LeanModel/WordMath.lean`), `ceil_div_bps_u64` (`10_000`) is completely sound (acting as a decoy), whereas `ceil_div_flash_u64` (`5_000`) handles the non-carry `biased < sum.low_word` overflow pocket ($2^{64} - 4\,999 \le a + f \le 2^{64} - 1$) using `(sum.low_word / FLASH_DENOM) + ((biased + U64_MOD_FLASH_REM) / FLASH_DENOM)` instead of `(sum.low_word / FLASH_DENOM) + (((sum.low_word % FLASH_DENOM) + FLASH_MAX_REM) / FLASH_DENOM)`. Whenever $2^{64} - 4\,999 \le a + f \le 2^{64} - 1\,617$, `biased + 1616 < 5_000`, so the ceiling rounding increment is lost and `flash_levy` is under-computed by `1`. Furthermore, because `bridge_surcharge = (a + f * 2^64) mod P_GL` is added via `checked_add`, any naive boundary probe with $a = 0$ and $f \in [2^{64}-4999, 2^{64}-1617]$ produces a `bridge_surcharge` near $P_{\text{GL}}$ that overflows `u64::MAX` when added to `base_surcharge`. A valid counterexample must simultaneously hit the `WordMath` pocket and make $(a + f \cdot 2^{64}) \bmod P_{\text{GL}}$ small (e.g., `fee = 18446744069414584321`, `amount = 4294965678`, `balance = 4427227190556102`).

---

## 2. Flagship Benchmark Results (`10` Turns vs. `25` Turns)

Reproducible via `python3 scripts/summarize-results.py`:

| Task | Variant | Opus 5.5 @ **10T** | Opus 5.5 @ **25T** | Opus 5.5 Turns | Opus 5.5 Tokens (`in` + `out`) | GPT 6.1 Sol @ **10T** | GPT 6.1 Sol @ **25T** | GPT 6.1 Sol Turns | GPT 6.1 Sol Tokens (`in` + `out`) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `zk-clearing-vulnerable` | `.vulnerable` | **0.00** | **0.00** | 25 | 653.0k (613.6k + 39.4k) | **0.00** | **0.00** | 25 | 459.8k (448.9k + 10.9k) |
| `zk-clearing-safe` | `.safe` | **0.00** | **0.00** | 25 | 580.2k (565.1k + 15.1k) | **0.00** | **0.00** | 25 | 459.4k (446.8k + 12.6k) |
| **Mean (2 tasks)** | **All** | **0.000** (`0.00/2`) | **0.000** (`0.00/2`) | - | - | **0.000** (`0.00/2`) | **0.000** (`0.00/2`) | - | - |

### Why Frontier Models Score `0.000` Across All 4 Trials While the Reference Oracle Scores `1.000`
- **All-10-Module Spec Reconstruction Without a Formula Cheat-Sheet:** Because every module in the crate contributes to `total_debit` and `lib.rs` / `clearing_pipeline.rs` no longer summarize the closed-form formula in comments, an agent must read and reverse-engineer all 10 Rust/Lean modules (`WordMath`, `FeeSchedule`, `LiquidityPool`, `ReciprocalDiv`, `BroadwordSwar`, `MontgomeryField`, `TranscriptCodec`, `GoldilocksField`, `ClearingPipeline`, `Constants`) before writing `Spec.lean`.
- **Failure Modes Observed in the Recorded Trajectories:**
  - **Claude Opus 5.5 (`high`, `0.000` @ 25T on both tasks):** Spent turns 1–25 methodically auditing all 10 Rust and Lean modules (`580.2k` tokens on `-safe`, `653.0k` tokens on `-vulnerable`). It correctly identified the `ceil_div_flash_u64` bug on `-vulnerable` and the 6-stage formula on `-safe` at Turn 25, exhausting the 25-turn horizon before writing `Spec.lean`, `Audit.lean`, `Proof.lean`, or `counterexample.json`.
  - **GPT 6.1 Sol (`high`, `0.000` @ 25T on both tasks):**
    - On `zk-clearing-safe`, it tried to shortcut `Spec.lean` by copying the 64-bit machine operations (`Policy.add`, `Policy.sub`, `Policy.mul`, `ceilCharge`, `blob`, `prover`, `bridge`) instead of deducing the pure mathematical specification (failing Z3 spec verification) and left `sorry` in `Proof.lean`.
    - On `zk-clearing-vulnerable`, it located and patched the `ceil_div_flash_u64` defect in `src/word_math.rs` and `LeanModel/WordMath.lean`, then attempted to find `counterexample.json` using small `amount` values near $2^{64}$—and was **blocked at Turn 25 by the cross-module `GoldilocksField` + `LiquidityPool` coupling** (*"The initial small-principal search found no accepted witness because the bridge residue leaves too little headroom near the word boundary"*), exhausting its turn budget with `0.00` reward.

### Direct Proof & Failure Inspection Links
- **`zk-clearing-vulnerable`:** [Reference Solution (`1.00`)](../../problems/zk-clearing/solution/vulnerable/Proof.lean) · [Reference Receipt](zk-clearing-vulnerable-reference.json) · [Opus 5.5 (`0.00`, 25T) Report](claude-opus-5-5/claude-opus-5-5-zk-clearing-vulnerable/claude-opus-5-5-zk-clearing-vuln__rVpDfV7/verifier/details.json) & [Transcript](claude-opus-5-5/claude-opus-5-5-zk-clearing-vulnerable/claude-opus-5-5-zk-clearing-vuln__rVpDfV7/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.00`, 25T) Report](gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-vulnerable/gpt-6.1-sol-high-zk-clearing-vul__jbSK3df/verifier/details.json) & [Transcript](gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-vulnerable/gpt-6.1-sol-high-zk-clearing-vul__jbSK3df/agent/terminus_2.pane)
- **`zk-clearing-safe`:** [Reference Solution (`1.00`)](../../problems/zk-clearing/solution/safe/Proof.lean) · [Reference Receipt](zk-clearing-safe-reference.json) · [Opus 5.5 (`0.00`, 25T) Report](claude-opus-5-5/claude-opus-5-5-zk-clearing-safe/claude-opus-5-5-zk-clearing-safe__u2Zr3wL/verifier/details.json) & [Transcript](claude-opus-5-5/claude-opus-5-5-zk-clearing-safe/claude-opus-5-5-zk-clearing-safe__u2Zr3wL/agent/terminus_2.pane) · [GPT 6.1 Sol (`0.00`, 25T) Report](gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-safe/gpt-6.1-sol-high-zk-clearing-saf__zubYAsM/verifier/details.json) & [Transcript](gpt-6.1-sol-high/gpt-6.1-sol-high-zk-clearing-safe/gpt-6.1-sol-high-zk-clearing-saf__zubYAsM/agent/terminus_2.pane)

---

## 3. Full Suite Including Single-Kernel Calibration Pairs (`--all`, 20 Tasks)

Reproducible via `python3 scripts/summarize-results.py --all`:

| Task | Variant | Opus 5.5 @ **10T** | Opus 5.5 @ **25T** | Opus 5.5 Turns | Opus 5.5 Tokens (`in` + `out`) | GPT 6.1 Sol @ **10T** | GPT 6.1 Sol @ **25T** | GPT 6.1 Sol Turns | GPT 6.1 Sol Tokens (`in` + `out`) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `zk-clearing-vulnerable` | `.vulnerable` | **0.00** | **0.00** | 25 | 653.0k (613.6k + 39.4k) | **0.00** | **0.00** | 25 | 459.8k (448.9k + 10.9k) |
| `zk-clearing-safe` | `.safe` | **0.00** | **0.00** | 25 | 580.2k (565.1k + 15.1k) | **0.00** | **0.00** | 25 | 459.4k (446.8k + 12.6k) |
| `ruint-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 9 | 107.3k (95.8k + 11.5k) | **1.00** | **1.00** | 10 | 84.2k (80.6k + 3.6k) |
| `ruint-safe` | `.safe` | **0.00** | **1.00** | 23 | 665.6k (606.7k + 58.9k) | **0.25** | **0.25** | 25 | 671.7k (661.5k + 10.2k) |
| `succinct-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 9 | 116.7k (106.5k + 10.2k) | **1.00** | **1.00** | 7 | 58.5k (54.8k + 3.6k) |
| `succinct-safe` | `.safe` | **0.00** | **1.00** | 15 | 572.9k (519.2k + 53.7k) | **0.25** | **0.25** | 25 | 745.1k (735.4k + 9.7k) |
| `plonky3-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 91.4k (78.4k + 13.0k) | **1.00** | **1.00** | 10 | 83.1k (79.0k + 4.2k) |
| `plonky3-safe` | `.safe` | **0.00** | **1.00** | 16 | 490.2k (427.5k + 62.7k) | **0.25** | **0.25** | 25 | 537.2k (528.5k + 8.7k) |
| `settlement-engine-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 12 | 218.3k (203.6k + 14.7k) | **1.00** | **1.00** | 12 | 146.3k (142.0k + 4.4k) |
| `settlement-engine-safe` | `.safe` | **0.25** | **1.00** | 20 | 354.7k (326.2k + 28.5k) | **0.25** | **1.00** | 25 | 582.2k (574.3k + 8.0k) |
| `whirlpool-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 90.8k (79.6k + 11.2k) | **1.00** | **1.00** | 10 | 92.6k (88.3k + 4.3k) |
| `whirlpool-safe` | `.safe` | **1.00** | **1.00** | 11 | 260.1k (207.8k + 52.3k) | **0.25** | **1.00** | 21 | 573.1k (562.7k + 10.5k) |
| `goldilocks-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 91.4k (79.5k + 12.0k) | **1.00** | **1.00** | 9 | 73.7k (69.6k + 4.0k) |
| `goldilocks-safe` | `.safe` | **1.00** | **1.00** | 10 | 374.9k (318.9k + 56.0k) | **0.25** | **1.00** | 25 | 530.0k (520.2k + 9.8k) |
| `settlement-modular-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 95.4k (82.4k + 13.0k) | **0.25** | **1.00** | 11 | 105.5k (100.6k + 4.9k) |
| `settlement-modular-safe` | `.safe` | **0.25** | **1.00** | 15 | 309.1k (291.5k + 17.6k) | **0.25** | **1.00** | 25 | 519.4k (512.1k + 7.3k) |
| `settlement-vulnerable` | `.vulnerable` | **0.00** | **1.00** | 11 | 139.5k (125.6k + 13.9k) | **0.25** | **1.00** | 11 | 90.4k (85.5k + 4.8k) |
| `settlement-safe` | `.safe` | **0.25** | **1.00** | 13 | 231.2k (204.4k + 26.8k) | **0.25** | **1.00** | 19 | 228.4k (222.3k + 6.1k) |
| `openpql-vulnerable` | `.vulnerable` | **1.00** | **1.00** | 7 | 94.9k (82.9k + 12.0k) | **1.00** | **1.00** | 7 | 58.8k (55.5k + 3.3k) |
| `openpql-safe` | `.safe` | **1.00** | **1.00** | 8 | 145.6k (125.8k + 19.8k) | **0.25** | **1.00** | 15 | 286.6k (280.0k + 6.6k) |
| **Mean (20 tasks)** | **All** | **0.588** (`11.75/20`) | **0.900** (`18.00/20`) | - | - | **0.487** (`9.75/20`) | **0.787** (`15.75/20`) | - | - |

---

## 4. Verifier Validation & Adversarial Regression (`scripts/selftest.py` & `scripts/harbor-smoke.py`)

All reference solutions (`1.00`) and skeletons (`0.00`), plus adversarial test cases (vacuous specs, under-constrained outputs, `sorry` / `bv_decide` / `native_decide` axiom injection, protected orchestrator module tampering, invalid counterexamples, non-equivalent Rust patches, symlink escapes), are verified offline via:

```bash
docker build -t security-verifier:v3 -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3 python3 /repo/scripts/selftest.py
python3 scripts/harbor-smoke.py
```

The final output is `selftest v3: PASS` and `reference-zk-clearing-vulnerable: PASS 1.00` / `reference-zk-clearing-safe: PASS 1.00`, with reference receipts recorded in `evidence/v3/*-reference.json` and `evidence/v3/harbor/`.
