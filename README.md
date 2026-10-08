# Rust authorization audit: a Lean-native, symmetric Harbor benchmark

Symmetric pairs of Harbor tasks ask an agent to specify a Rust payment
authorization function in Lean, decide whether it conforms to its documented
policy over the full `u64` domain, and justify that decision.
All tasks receive byte-identical instructions. In each pair, one implementation
is vulnerable to subtle unsigned arithmetic bugs (CWE-190 / CWE-682); the other
is universally correct. A fixed verdict therefore cannot score well on both.

## Task pairs

| Task | Isolation level & codebase size | Arithmetic kernel & policy | Expected verdict |
|---|---|---|---|
| `lfglabs/authorization-vulnerable` | Isolated (~40 lines Rust / ~40 lines Lean) | `amount.wrapping_add(fee)` vs mathematical `amount + fee` | `.vulnerable` |
| `lfglabs/authorization-safe` | Isolated (~40 lines Rust / ~40 lines Lean) | `amount.checked_add(fee)?` vs mathematical `amount + fee` | `.safe` |
| `lfglabs/settlement-vulnerable` | **Level 0 — Isolated kernel** (~80 lines Rust / ~55 lines Lean) | Pure-`u64` ceiling basis-point fee (`⌈(amount + fee)/10_000⌉`) minus floor tier rebate (`⌊gross/10⌋`) with an interior carry-pocket off-by-one when `2^64 - 9_999 ≤ amount + fee ≤ 2^64 - 1_617` | `.vulnerable` |
| `lfglabs/settlement-safe` | **Level 0 — Isolated kernel** (~80 lines Rust / ~55 lines Lean) | Same two-stage settlement policy with exact quotient/remainder decomposition across both wrap boundaries | `.safe` |
| `lfglabs/settlement-modular-vulnerable` | **Level 1 — Modular pipeline** (~195 lines Rust / ~105 lines Lean across 4 modules: `constants`, `bps_math`, `rebate`, `quote`) | Same policy decomposed across `fold_u64_sum` → `ceil_div_bps_folded` → `compute_fee_breakdown` → `build_settlement_quote` → `verify_affordability`; the bug emerges from the interaction between `SumFold` and `ceil_div_bps_folded` | `.vulnerable` |
| `lfglabs/settlement-modular-safe` | **Level 1 — Modular pipeline** (~195 lines Rust / ~105 lines Lean across 4 modules) | Universally conforming modular pipeline | `.safe` |
| `lfglabs/settlement-engine-vulnerable` | **Level 2 — Full engine with realistic noise** (~330 lines Rust / ~180 lines Lean across 6 modules: `constants`, `word_math`, `fee_tiers`, `liquidity_pool`, `flash_loan`, `settlement_engine`) | Full DeFi settlement engine with 7 structs and 14 functions, including 6 sibling 64-bit fee/rounding calculators (`assess_flash_fee_ceil`, `evaluate_passive_floor_fee`, `split_pool_reserve`, `compute_capped_maker_rebate`, etc.) that are 100% sound red herrings | `.vulnerable` |
| `lfglabs/settlement-engine-safe` | **Level 2 — Full engine with realistic noise** (~330 lines Rust / ~180 lines Lean across 6 modules) | Universally conforming full settlement engine | `.safe` |
| `lfglabs/goldilocks-vulnerable` | **RVB-excluded kernel — Goldilocks prime reduction** (`recmo/goldilocks` `ntt/src/field/algo/generic.rs`, `reduce_128` / `reduce_159` over $P = 2^{64} - 2^{32} + 1$) | Two-step 128-bit Goldilocks reduction `(x0 + x1 · 2^64) mod P` using `2^64 ≡ 2^32 - 1 (mod P)` where the final canonicalization branch checks `> P` instead of `≥ P`, leaving a single unreduced value `r = P` when `x1_hi + b1 · ε` lands on `P` | `.vulnerable` |
| `lfglabs/goldilocks-safe` | **RVB-excluded kernel — Goldilocks prime reduction** (`recmo/goldilocks`) | Universally canonical Goldilocks reduction `reduce_128` over all `(balance, amount, fee) ∈ u64^3` | `.safe` |
| `lfglabs/whirlpool-vulnerable` | **RVB-excluded kernel — Multi-word `U128Muldiv` ceiling division** (`orca-so/whirlpools` `programs/whirlpool/src/math/u256_math.rs`, 4-word base-$2^{32}$ `div` + `div_round_up_if`) | 4-limb base-$2^{32}$ division of `amount + fee · 2^64` by `FEE_RATE_MUL_VALUE = 1_000_000` with quotient round-up carry propagation (`add_carry`) that omits the `w1 → w2` carry when `q0 = 2^32 - 1`, `q1 = 2^32 - 1` and `rem > 0`, wrapping a $2^{64}$ quotient to `0` | `.vulnerable` |
| `lfglabs/whirlpool-safe` | **RVB-excluded kernel — Multi-word `U128Muldiv` ceiling division** (`orca-so/whirlpools`) | Universally conforming 4-word `U128Muldiv` ceiling division and carry chain across all 4 limbs | `.safe` |
| `lfglabs/plonky3-vulnerable` | **RVB-excluded kernel — BabyBear 64-bit Montgomery reduction** (`Plonky3/Plonky3` `monty-31/src/utils.rs`, `to_monty_64` + `monty_reduce` over $P = 2\,013\,265\,921$) | 64-bit Montgomery reduction `((amount mod 2^32) + (fee mod P) · 2^32) · R^{-1} mod P` (`R = 2^32`, `MU = P^{-1} mod 2^32 = 2_281_701_377`) where the unsigned underflow branch adds `(1 << 32) - P` instead of `P` after shifting by 32 bits | `.vulnerable` |
| `lfglabs/plonky3-safe` | **RVB-excluded kernel — BabyBear 64-bit Montgomery reduction** (`Plonky3/Plonky3`) | Universally conforming 64-bit BabyBear Montgomery reduction `to_monty_64` + `monty_reduce` | `.safe` |
| `lfglabs/succinct-vulnerable` | **Non-Web3 SWAR kernel — Vigna broadword byte detection** (`tov/succinct-rs` `src/broadword.rs`, `u_nz8` + `count_nz_bytes` + `sum_bytes`) | SWAR parallel 8-byte non-zero detection `u_nz8(x) = (((x \| H8) - L8) \| x) & H8` and 16-bit lane folding `sum_bytes(x)` where omitting `\| x` in `u_nz8(x)` misses every byte equal to `0x80` (`128`), under-computing the surcharge by `256` per `0x80` byte | `.vulnerable` |
| `lfglabs/succinct-safe` | **Non-Web3 SWAR kernel — Vigna broadword byte detection** (`tov/succinct-rs`) | Universally conforming SWAR broadword byte-count and byte-sum settlement kernel | `.safe` |
| `lfglabs/openpql-vulnerable` | **Non-Web3 combinatorial kernel — 4-level mixed-radix indexing** (`solve-poker/Poker-Query-Language` `openpql-range-parser/src/waugh_indexer/mixed_radix.rs`, `encode` + `clamp_digit`) | 4-level mixed-radix positional encoding with radices `(32768, 65536, 65536, 131072)` where computing `space_size = o0.wrapping_mul(b0) = 65536^4 ≡ 0 (mod 2^64)` wraps the capacity guard `if raw_idx < space_size` to `false`, zeroing the surcharge on `fee = u64::MAX` | `.vulnerable` |
| `lfglabs/openpql-safe` | **Non-Web3 combinatorial kernel — 4-level mixed-radix indexing** (`solve-poker/Poker-Query-Language`) | Universally conforming 4-level mixed-radix positional encoding over all `u64` inputs | `.safe` |
| `lfglabs/ruint-vulnerable` | **Web3 multi-precision kernel — Möller-Granlund 2-by-1 normalized division** (`alloy-rs/ruint` `src/algorithms/div/small.rs`, `div_2x1_mg10`) | Möller-Granlund reciprocal division `⌊(u1 · 2^16 + u0) / D⌋` for normalized divisor `D = 0x8003 = 32771` and reciprocal `V = 0xFFF4 = 65524` where omitting the second conditional remainder correction `if r_corr >= D` under-estimates the quotient by `1` whenever `r_corr ∈ [D, 2D)` | `.vulnerable` |
| `lfglabs/ruint-safe` | **Web3 multi-precision kernel — Möller-Granlund 2-by-1 normalized division** (`alloy-rs/ruint`) | Universally conforming Möller-Granlund 2-by-1 normalized division over all `u64` inputs | `.safe` |

Within each pair, everything else in the prompt and API is shared, including the
unit tests (which pass on both `.vulnerable` and `.safe`). Apart from the task
name, only the original Rust, its visible Lean model
(`SecurityChallenge.challengeAuthorize`), the reference solution and the
verifier's trusted `variant.txt`/`problem.txt` differ.

- In **`authorization`**, `S = amount + fee`, and `(balance, amount, fee) = (0, 2^64-1, 1)` makes the vulnerable code authorize a debit of `0`.
- In **`settlement` / `settlement-modular` / `settlement-engine`** (inspired by concentrated-liquidity fee/rebate kernels and pure-`u64` modular carry folding in `lfglabs-dev/rust-verification-benchmark`: `orca-so/whirlpools`, `DarkOtter/indexed-bitvec-rs` and `recmo/goldilocks`), the mathematical settlement debit is:
  $$\text{gross\_fee} = \left\lceil \frac{\text{amount} + \text{fee}}{10\,000} \right\rceil, \quad \text{rebate} = \left\lfloor \frac{\text{gross\_fee}}{10} \right\rfloor, \quad S = \text{amount} + (\text{gross\_fee} - \text{rebate}).$$
  Because $2^{64} = 1\,844\,674\,407\,370\,955 \times 10\,000 + 1\,616$, the vulnerable `if biased < raw_sum` branch (`(raw_sum / 10_000) + ((biased + 1_616) / 10_000)`) is exact at `u64::MAX` (`amount + fee ∈ [2^64 - 1_616, 2^64 - 1]`) and across `amount + fee ≥ 2^64`, but under-computes `gross_fee` and `net_fee` by `1` strictly inside the interior pocket `2^64 - 9_999 ≤ amount + fee ≤ 2^64 - 1_617` (width `8_383` out of `2^64`, e.g. `(balance, amount, fee) = (1_660_206_966_635_476, 1_617, 18_446_744_073_709_540_000)`).
  The three isolation levels (`settlement`, `settlement-modular`, `settlement-engine`) share this exact mathematical policy and evaluate how progressive code dispersion and surrounding domain noise affect formal specification, bug localization, and Lean 4 proof construction.
- In **`goldilocks`**, **`whirlpool`**, **`plonky3`**, **`succinct`**, **`openpql`**, and **`ruint`**, the arithmetic kernels are drawn directly from real crates in the `rust-verification-benchmark` upstream repositories (`recmo/goldilocks`, `orca-so/whirlpools`, `Plonky3/Plonky3`, `tov/succinct-rs`, `solve-poker/Poker-Query-Language`, `alloy-rs/ruint`) whose core bit-manipulation, mixed-radix, or reciprocal-division invariants were excluded from RVB as `too_complex` or harbor real upstream boundary bugs:
  - **`goldilocks`** (`recmo/goldilocks` `reduce_128`): $P = 2^{64} - 2^{32} + 1 = 18\,446\,744\,069\,414\,584\,321$,
    $$S = \left\lfloor \frac{\text{amount}}{2^{32}} \right\rfloor + \left(\left(\text{amount} + \text{fee} \cdot 2^{64}\right) \bmod P\right).$$
  - **`whirlpool`** (`orca-so/whirlpools` `U128Muldiv::div` + `div_round_up_if`):
    $$S = \left\lfloor \frac{\text{amount}}{2} \right\rfloor + \left\lceil \frac{\text{amount} + \text{fee} \cdot 2^{64}}{1\,000\,000} \right\rceil.$$
  - **`plonky3`** (`Plonky3/Plonky3` `to_monty_64` + `monty_reduce`): $P = 2\,013\,265\,921$, $R = 2^{32}$, $R^{-1} \bmod P = 943\,718\,400$,
    $$S = \text{amount} + \left(\left(\left(\text{amount} \bmod 2^{32}\right) + \left(\text{fee} \bmod P\right) \cdot 2^{32}\right) \cdot 943\,718\,400 \bmod P\right).$$
  - **`succinct`** (`tov/succinct-rs` `broadword.rs`, Non-Web3 SWAR kernel): for bytes $b_i(\text{fee}) = \lfloor \text{fee} / 256^i \rfloor \bmod 256$ ($i \in \{0,\dots,7\}$),
    $$S = \left\lfloor \frac{\text{amount}}{2} \right\rfloor + \sum_{i=0}^{7} b_i(\text{fee}) + 256 \cdot \left|\left\{i \in \{0,\dots,7\} \mid b_i(\text{fee}) > 0\right\}\right|.$$
  - **`openpql`** (`solve-poker/Poker-Query-Language` `mixed_radix.rs`, Non-Web3 combinatorial indexing kernel): for digits $d_0 = \min(\text{fee} \bmod 65536, 32767)$, $d_1 = \lfloor \text{fee} / 2^{16} \rfloor \bmod 65536$, $d_2 = \lfloor \text{fee} / 2^{32} \rfloor \bmod 65536$, $d_3 = \lfloor \text{fee} / 2^{48} \rfloor \bmod 65536$, and mixed-radix index $I(\text{fee}) = d_0 \cdot 2^{49} + d_1 \cdot 2^{33} + d_2 \cdot 2^{17} + d_3$,
    $$S = \left\lfloor \frac{\text{amount}}{2} \right\rfloor + \left\lfloor \frac{I(\text{fee})}{2^{49}} \right\rfloor = \left\lfloor \frac{\text{amount}}{2} \right\rfloor + \min(\text{fee} \bmod 65536, 32767).$$
  - **`ruint`** (`alloy-rs/ruint` `algorithms/div/small.rs`, Web3 Möller-Granlund 2-by-1 normalized division kernel): for normalized divisor $D = 32771$ (`0x8003`), base $B = 2^{16} = 65536$, $u_1 = \text{fee} \bmod D$, and $u_0 = \text{amount} \bmod B$,
    $$S = \left\lfloor \frac{\text{amount}}{2} \right\rfloor + \left\lfloor \frac{u_1 \cdot 65536 + u_0}{32771} \right\rfloor.$$

## Agent contract

**Visible to the agent:** `/workspace/challenge` (the Rust crate with ordinary
tests), `/workspace/lean/SecurityChallenge.lean` (the API, the visible model and
`AuditClaim`) and `python3 /workspace/lean/check.py` (a local compile check).
Prebuilt **Mathlib** (along with `Batteries`, `Aesop`, `Qq`, `Std`, and `Init`)
is installed in `/opt/rvb-deps` in both the agent container and the verifier
container and exposed on `LEAN_PATH`.
The reference policy, the semantic checker and the pristine Rust live only in
the verifier image. The runtime has no network access (`allow_internet = false`).
The agent has 2 h; the verifier has 20 min.

**Required outputs** in `/workspace/submission/`:

| File | Content |
|---|---|
| `Spec.lean` | Lean module defining `candidateSpec : AuthorizationSpec`, with `accepts : UInt64 → UInt64 → UInt64 → Prop` (balance, amount, fee) and `output : UInt64 → UInt64 → UInt64 → UInt64 → Prop` (… , totalDebit) |
| `Audit.lean` | Lean module defining `verdict : AuditVerdict` (`.vulnerable` or `.safe`) |
| `Proof.lean` | A proof **term** of `AuditClaim candidateSpec verdict`. This is `Conforms candidateSpec challengeAuthorize` if safe, and its negation if vulnerable |
| `counterexample.json` | Vulnerable only: `{"balance": …, "amount": …, "fee": …}` as decimal `u64` integers |
| `src/lib.rs` | Vulnerable only: a repaired crate that keeps the public API |

For a safe verdict, `counterexample.json` and `src/lib.rs` must be **absent**.
Lean sources may import `SecurityChallenge`, `Lean`, `Std`, `Init`, `Mathlib.*`,
`Batteries.*`, `Aesop.*`, and `Qq.*`. They may not use `sorry`, `axiom`, `native_decide`,
`unsafe`, `extern`/`implemented_by`, `initialize` or syntax/macro/elab
extensions. `Proof.lean` may not declare top-level declarations itself; the verifier wraps it
in a fixed theorem (auxiliary lemmas and helper definitions can be placed in `Spec.lean` or `Audit.lean`).

## Grading

Every artifact must be a regular file of at most 64 KiB; symlinks are rejected.
Grading is fail-closed. Each checkpoint reports one of `pass`, `partial`,
`fail`, `missing`, `unsupported`, `timeout`, `unknown` or
`infrastructure_error`, and only `pass` (or partial credit) earns points.

### Lean pipeline

`Spec.lean`, `Audit.lean` and `Proof.lean` are compiled in that order (with `-M4096`). Each
stage runs in a fresh directory under a Landlock+seccomp sandbox without network
access, and drops to uid 65534 when started as root. Only the serialized
`.olean` from each stage is kept. `leanchecker` then independently replays its kernel declarations, and a
trusted auditor (`SpecAudit.lean`, loaded with `loadExts := false`) checks the
expected type and the transitive axioms. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. Any kernel-accepted proof works; `omega` is not
required.

### Semantic specification grading

The auditor lowers the elaborated `accepts` and `output` expressions into a typed
arithmetic tree. It unfolds auxiliary definitions, `let`, beta-redexes and
structure projections. Z3 then decides each obligation over the full `u64` input
domain (using Euclidean quotient/remainder purification for large modular/limb
divisors). The model's text is never compared.

- **Supported fragment:** `UInt64.toNat` of an input, `Nat` literals, `+`,
  truncated `-`, `*`, constant `^`, constant `/` and `%`, bitwise `&&&`/`|||`/`^^^`/`<<<`/`>>>`,
  `=`, `<`, `≤`, `∧`, `∨`, `¬`, `↔`, non-dependent `→` and non-dependent `if`.
- **Unsupported:** raw `UInt64` arithmetic without `.toNat`, division/modulo by a non-constant,
  quantifiers, recursors and other heads. These yield `unsupported` for the
  affected facets, not "wrong". There is no fallback for arbitrary Lean.
  `unknown` and `timeout` (10 s per query) earn no credit.

For mathematical settlement debit $S$ (computed in unbounded integers), the
hidden contract is `accept ⇔ S ≤ balance`, with `totalDebit = S` on acceptance.
Because `balance` is a `u64`, `S ≤ balance` also rules out `u64` output overflow.
The spec has four equally weighted facets:

1. **Safety:** `accepts → S ≤ balance`.
2. **Completeness:** `S ≤ balance → accepts`.
3. **Output exactness:** on accepted inputs, every allowed output equals
   `S`, and the output is unique. This facet also requires facet 4.
4. **Existence/coherence:** `accepts` is satisfiable, and every accepted input has
   some `u64` output.

So an all-`False` spec earns only facet 1, which is 6.25 of 100 points.

### Rust grading

`rust_symbolic.py` parses a documented subset of Rust and proves, with Z3 over all
`u64` inputs, that `Some` holds iff `S ≤ balance` and that `total_debit = S`.

- **Supported subset:** inline modules, decimal and hexadecimal integer constants,
  plain structs, tuples and tuple destructuring, non-recursive helper functions
  (symbolically inlined across modules), `let`, `let mut`, variable assignment and shadowing,
  `if`/`else`, `if let`, exhaustive `Option` matches, `return`, `?`, `u32`/`u64`
  (and `u128` when permitted by the crate contract; forbidden in pure-`u64` kernels),
  `+`/`-`/`*`/`/`/`%`, bitwise `&`/`|`/`^` and constant shifts `<<`/`>>`,
  comparisons and booleans, `div_ceil`, `checked_`/`wrapping_`/`overflowing_`
  add, sub and mul, `checked_` div and rem, `saturating_` add and sub,
  `then_some`, built-in derives and `#[cfg(test)]` modules.
- **Rejected before execution:** loops, macros, `unsafe`, crate attributes and
  external dependencies.

The code is then compiled (`rustc -O`, overflow checks off) and run on concrete
boundary and random cases, including any SMT counterexample. A witness passes
only if the verifier's own pristine build violates the mathematical contract on
that triple.

## Scoring

Reward is the sum of four checkpoints, from 0 to 1:

| Checkpoint | Weight | Vulnerable task | Safe task |
|---|---:|---|---|
| Specification | 0.25 | 0.0625 per facet passed | same |
| Verdict | 0.15 | `verdict = .vulnerable` | `verdict = .safe` **and** proof passes **and** the pristine Rust passes the universal check |
| Lean evidence | 0.25 | `AuditClaim candidateSpec verdict` kernel-checked | same |
| Response | 0.35 | Witness 0.15 + universally correct repair 0.20 | Same conditions as the verdict, plus no witness/repair files |

The checkpoints are independent. A malformed spec does not block the
witness/repair credit, and a bare `safe` earns nothing. Lean evidence covers the
**submitted spec over the visible original model**. A proof about a weak spec can
still earn 0.25 while the spec facets fail; `details.json` records that scope.

Harbor reads `/logs/verifier/reward.txt`. Per-facet results, Z3 counterexamples,
diagnostics and artifact SHA-256s are written to `/logs/verifier/details.json`.

## Running

Requirements: Docker with Compose v2, Python 3.12+, and access to the pinned base
images.

```bash
git clone https://github.com/Th0rgal/rust-security-verification-harbor
cd rust-security-verification-harbor
python3 -m venv .venv && .venv/bin/pip install -r scripts/harbor-requirements.lock
python3 scripts/make-family.py /tmp/security-family   # generates all 10 pairs (or pass --problem <name>)

# Oracle (reference) runs; Harbor builds the agent and the separate verifier image.
for p in authorization settlement settlement-modular settlement-engine goldilocks whirlpool plonky3 succinct openpql ruint; do
  for v in vulnerable safe; do
    .venv/bin/harbor run -p /tmp/security-family/$p-$v -a oracle -e docker -n 1
  done
done
```

To evaluate a model, replace `-a oracle` with any Harbor agent and model, for
example `-a terminus-2 -m <model>`. Run **both** tasks of each pair and report
each reward, along with the mean. If you pin `docker_image` in `task.toml`, use
the task-specific image for each variant, because the variants' images differ.

Reference end-to-end check, which builds fresh images, runs the reference
oracles, asserts 1.00 and identical prompts, and checks artifact hashes after
Harbor's copy:

```bash
.venv/bin/python scripts/harbor-smoke.py --harbor .venv/bin/harbor --output /tmp/v3-e2e
```

Adversarial regression suite (equivalent/weak/vacuous/unsupported specs,
Mathlib imports, correct and incorrect Rust repairs across families, hostile
Lean, sandbox isolation, independent scoring, all 20 reference tasks):

```bash
docker build -t security-verifier:v3-review -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3-review python3 /repo/scripts/selftest.py   # ends with "selftest v3: PASS"
```

If Docker runs on another host, put Harbor's jobs directory on a filesystem
shared with that host, because verifier logs are bind-mounted.

## Evidence and baseline status

- **References:** `evidence/v3/` records reference verification reports with `1.00`
  across all 20 task variants (`authorization`, `settlement`, `settlement-modular`,
  `settlement-engine`, `goldilocks`, `whirlpool`, `plonky3`, `succinct`, `openpql`, `ruint`),
  plus the `selftest v3: PASS` suite.
- **GLM 5.3 Flash (`authorization`):** fresh Harbor 0.9.0 runs with `terminus-2` and
  `zai/glm-5.3-flash` scored **1.00 on each `authorization` v3 task** (mean 1.00). Both trials
  passed all four checkpoints: spec 0.25, verdict 0.15, proof 0.25 and response
  0.35. Complete trajectories, terminal recordings, submitted artifacts and
  verifier reports are in `evidence/v3/glm-5.3-flash/`.
- **Claude Opus 5.5 & GPT 6.1 Sol (`high`) across the 3 `settlement` isolation levels & 6 RVB-derived arithmetic kernels (`36` Harbor 0.9.0 trials):**
  fresh Harbor 0.9.0 runs via `sandboxed.sh` (`terminus-2`, `reasoning_effort=high`, `max_turns=25`)
  evaluated both models on all six `settlement*` tasks and all twelve RVB-derived kernel tasks
  (`goldilocks`, `whirlpool`, `plonky3`, `succinct`, `openpql`, `ruint` in both `vulnerable` and `safe` variants).
  **Claude Opus 5.5** achieved **18 / 18 at `1.00`** (**mean `1.000`**), whereas **GPT 6.1 Sol (`high`)**
  achieved **15 / 18 at `1.00`** and scored **`0.25` on three `.safe` universal proof tasks** (**mean `0.875`** overall, **`0.750`** on the 6 new non-Web3 + Web3 tasks):
  - **`plonky3-safe`**: Opus 5.5 closed the Lean 4 universal `Conforms` proof over the 64-bit BabyBear Montgomery reduction pipeline in 16 episodes (**1.00**); GPT 6.1 Sol (`high`) passed only the specification checkpoint (**0.25**) and left `by sorry` after 25 episodes.
  - **`succinct-safe` (Non-Web3 SWAR broadword kernel)**: Opus 5.5 proved Vigna's parallel 8-byte non-zero detection and 16-bit lane-summation identity in kernel-pure Lean 4 in 15 episodes (**1.00**); GPT 6.1 Sol (`high`) passed only the specification checkpoint (**0.25**) and relied on `bv_decide` (`count_correct._native.bv_decide.ax_1_5`), which the transitive axiom auditor rejected.
  - **`ruint-safe` (Web3 Möller-Granlund 2-by-1 normalized division kernel)**: Opus 5.5 proved the universal equivalence between `div_2x1_mg10` (`V = 0xFFF4`, `D = 0x8003`, `SUB_BIAS = 0xC000_0000`) and `⌊(u1 · 2^16 + u0) / 32771⌋` in 23 episodes (**1.00**); GPT 6.1 Sol (`high`) passed only the specification checkpoint (**0.25**) and exhausted 25 episodes without discharging the `omega` obligation on the reciprocal approximation.
  Complete trajectories, terminal recordings, submitted artifacts and verifier reports are in
  `evidence/v3/claude-opus-5-5/` and `evidence/v3/gpt-6.1-sol-high/`:

| Task | Category / Isolation level | Model | Reward | Episodes | Input / Output tokens |
|---|---|---|---:|---:|---:|
| `settlement-vulnerable` | Level 0 — Isolated | `claude-opus-5-5` | **1.00** | 11 | 125,566 / 13,927 |
| `settlement-safe` | Level 0 — Isolated | `claude-opus-5-5` | **1.00** | 13 | 204,438 / 26,781 |
| `settlement-modular-vulnerable` | Level 1 — Modular (4 modules) | `claude-opus-5-5` | **1.00** | 7 | 82,393 / 13,037 |
| `settlement-modular-safe` | Level 1 — Modular (4 modules) | `claude-opus-5-5` | **1.00** | 15 | 291,454 / 17,616 |
| `settlement-engine-vulnerable` | Level 2 — Engine + noise (6 modules) | `claude-opus-5-5` | **1.00** | 12 | 203,563 / 14,746 |
| `settlement-engine-safe` | Level 2 — Engine + noise (6 modules) | `claude-opus-5-5` | **1.00** | 20 | 326,168 / 28,548 |
| `goldilocks-vulnerable` | RVB-excluded — Goldilocks `reduce_128` | `claude-opus-5-5` | **1.00** | 7 | 79,463 / 11,963 |
| `goldilocks-safe` | RVB-excluded — Goldilocks `reduce_128` | `claude-opus-5-5` | **1.00** | 10 | 318,916 / 56,012 |
| `whirlpool-vulnerable` | RVB-excluded — 4-word `U128Muldiv::div` | `claude-opus-5-5` | **1.00** | 7 | 79,589 / 11,214 |
| `whirlpool-safe` | RVB-excluded — 4-word `U128Muldiv::div` | `claude-opus-5-5` | **1.00** | 11 | 207,795 / 52,294 |
| `plonky3-vulnerable` | RVB-excluded — BabyBear `monty_reduce` | `claude-opus-5-5` | **1.00** | 7 | 78,368 / 13,025 |
| `plonky3-safe` | RVB-excluded — BabyBear `monty_reduce` | `claude-opus-5-5` | **1.00** | 16 | 427,455 / 62,738 |
| `succinct-vulnerable` | Non-Web3 SWAR — `succinct-rs` `u_nz8` | `claude-opus-5-5` | **1.00** | 9 | 106,468 / 10,245 |
| `succinct-safe` | Non-Web3 SWAR — `succinct-rs` `u_nz8` | `claude-opus-5-5` | **1.00** | 15 | 519,172 / 53,691 |
| `openpql-vulnerable` | Non-Web3 indexing — `openpql` `mixed_radix` | `claude-opus-5-5` | **1.00** | 7 | 82,887 / 11,988 |
| `openpql-safe` | Non-Web3 indexing — `openpql` `mixed_radix` | `claude-opus-5-5` | **1.00** | 8 | 125,803 / 19,838 |
| `ruint-vulnerable` | Web3 multi-precision — `ruint` `div_2x1_mg10` | `claude-opus-5-5` | **1.00** | 9 | 95,791 / 11,518 |
| `ruint-safe` | Web3 multi-precision — `ruint` `div_2x1_mg10` | `claude-opus-5-5` | **1.00** | 23 | 606,715 / 58,861 |
| `settlement-vulnerable` | Level 0 — Isolated | `gpt-6.1-sol` (`high`) | **1.00** | 11 | 85,546 / 4,823 |
| `settlement-safe` | Level 0 — Isolated | `gpt-6.1-sol` (`high`) | **1.00** | 19 | 222,260 / 6,129 |
| `settlement-modular-vulnerable` | Level 1 — Modular (4 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 11 | 100,604 / 4,862 |
| `settlement-modular-safe` | Level 1 — Modular (4 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 25 | 512,074 / 7,345 |
| `settlement-engine-vulnerable` | Level 2 — Engine + noise (6 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 12 | 141,956 / 4,373 |
| `settlement-engine-safe` | Level 2 — Engine + noise (6 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 25 | 574,267 / 7,982 |
| `goldilocks-vulnerable` | RVB-excluded — Goldilocks `reduce_128` | `gpt-6.1-sol` (`high`) | **1.00** | 9 | 69,649 / 4,035 |
| `goldilocks-safe` | RVB-excluded — Goldilocks `reduce_128` | `gpt-6.1-sol` (`high`) | **1.00** | 25 | 520,160 / 9,804 |
| `whirlpool-vulnerable` | RVB-excluded — 4-word `U128Muldiv::div` | `gpt-6.1-sol` (`high`) | **1.00** | 10 | 88,279 / 4,306 |
| `whirlpool-safe` | RVB-excluded — 4-word `U128Muldiv::div` | `gpt-6.1-sol` (`high`) | **1.00** | 21 | 562,674 / 10,471 |
| `plonky3-vulnerable` | RVB-excluded — BabyBear `monty_reduce` | `gpt-6.1-sol` (`high`) | **1.00** | 10 | 78,958 / 4,180 |
| `plonky3-safe` | RVB-excluded — BabyBear `monty_reduce` | `gpt-6.1-sol` (`high`) | **0.25** | 25 | 528,461 / 8,735 |
| `succinct-vulnerable` | Non-Web3 SWAR — `succinct-rs` `u_nz8` | `gpt-6.1-sol` (`high`) | **1.00** | 7 | 54,849 / 3,645 |
| `succinct-safe` | Non-Web3 SWAR — `succinct-rs` `u_nz8` | `gpt-6.1-sol` (`high`) | **0.25** | 25 | 735,370 / 9,736 |
| `openpql-vulnerable` | Non-Web3 indexing — `openpql` `mixed_radix` | `gpt-6.1-sol` (`high`) | **1.00** | 7 | 55,481 / 3,283 |
| `openpql-safe` | Non-Web3 indexing — `openpql` `mixed_radix` | `gpt-6.1-sol` (`high`) | **1.00** | 15 | 279,952 / 6,609 |
| `ruint-vulnerable` | Web3 multi-precision — `ruint` `div_2x1_mg10` | `gpt-6.1-sol` (`high`) | **1.00** | 10 | 80,556 / 3,603 |
| `ruint-safe` | Web3 multi-precision — `ruint` `div_2x1_mg10` | `gpt-6.1-sol` (`high`) | **0.25** | 25 | 661,513 / 10,224 |

- The historical GLM submission scored 0.00 on v1. Replaying its unchanged
  artifacts under v2 JSON grading produced 0.60; that replay remains in
  `scripts/fixtures/glm-5.3-flash/` and is not a v3 result.

## Trust boundary and limits

- The Lean theorem concerns the visible model, not the Rust. The correspondence
  between the Rust and the model, and the soundness of `rust_symbolic.py` on its
  subset, are reviewed and regression-tested rather than kernel-proved.
- Repaired Rust is judged only by the SMT backend plus compiled probes. Code
  outside the subset is `unsupported` even if it is correct.
- Specification grading is complete only for the fragment listed above.
- The claims are functional: authorization and debit correctness for every
  `u64` triple. They say nothing about timing, panics outside the subset or
  other properties.

See [BACKEND.md](BACKEND.md) for the full verifier semantics and isolation
design.

## Layout

```
task/                           shared task kernel & authorization-vulnerable source
problems/settlement/            Level 0 isolated settlement-{vulnerable,safe} sources & solutions
problems/settlement-modular/    Level 1 modular settlement-modular-{vulnerable,safe} sources & solutions
problems/settlement-engine/     Level 2 noisy crate settlement-engine-{vulnerable,safe} sources & solutions
problems/goldilocks/            RVB-excluded Goldilocks reduce_128 goldilocks-{vulnerable,safe} sources & solutions
problems/whirlpool/             RVB-excluded Orca Whirlpool U128Muldiv whirlpool-{vulnerable,safe} sources & solutions
problems/plonky3/               RVB-excluded Plonky3 BabyBear monty_reduce plonky3-{vulnerable,safe} sources & solutions
problems/succinct/              Non-Web3 SWAR broadword succinct-{vulnerable,safe} sources & solutions
problems/openpql/               Non-Web3 mixed-radix indexing openpql-{vulnerable,safe} sources & solutions
problems/ruint/                 Web3 Möller-Granlund 2-by-1 division ruint-{vulnerable,safe} sources & solutions
scripts/make-family.py          generates all 10 symmetric task pairs (20 Harbor tasks)
scripts/references/             authorization-safe reference proof
scripts/selftest.py             adversarial regression suite covering all 10 task pairs
scripts/harbor-smoke.py         Harbor E2E check of reference task pairs
evidence/v3/                    current-version validation; other evidence/ entries are v1/v2
evidence/v3/glm-5.3-flash       complete GLM 5.3 Flash v3 Harbor runs and traces
evidence/v3/claude-opus-5-5     complete Claude Opus 5.5 v3 Harbor runs and traces (18 tasks)
evidence/v3/gpt-6.1-sol-high    complete GPT 6.1 Sol (high) v3 Harbor runs and traces (18 tasks)
```



