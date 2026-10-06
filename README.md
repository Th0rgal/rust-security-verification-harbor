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

## Agent contract

**Visible to the agent:** `/workspace/challenge` (the Rust crate with ordinary
tests), `/workspace/lean/SecurityChallenge.lean` (the API, the visible model and
`AuditClaim`) and `python3 /workspace/lean/check.py` (a local compile check).
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
Lean sources may import only `SecurityChallenge`, `Lean`, `Std` and
`Lean.Elab.Tactic.Omega`. They may not use `sorry`, `axiom`, `native_decide`,
`unsafe`, `extern`/`implemented_by`, `initialize` or syntax/macro/elab
extensions. `Proof.lean` may not declare anything itself; the verifier wraps it
in a fixed theorem.

## Grading

Every artifact must be a regular file of at most 64 KiB; symlinks are rejected.
Grading is fail-closed. Each checkpoint reports one of `pass`, `partial`,
`fail`, `missing`, `unsupported`, `timeout`, `unknown` or
`infrastructure_error`, and only `pass` (or partial credit) earns points.

### Lean pipeline

`Spec.lean`, `Audit.lean` and `Proof.lean` are compiled in that order. Each
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
domain. The model's text is never compared.

- **Supported fragment:** `UInt64.toNat` of an input, `Nat` literals, `+`,
  truncated `-`, constant `*`, `/` and `%`, `=`, `<`, `≤`, `∧`, `∨`, `¬`, `↔`,
  non-dependent `→` and non-dependent `if`.
- **Unsupported:** `UInt64` arithmetic, nonlinear variable multiplication/division,
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

- **Supported subset:** inline modules, integer constants, plain structs and
  non-recursive helper functions (symbolically inlined in `settlement*` tasks),
  `let` and shadowing, `if`/`else`, `if let`, exhaustive `Option` matches,
  `return`, `?`, casts (when permitted by the crate contract; forbidden in
  pure-`u64` `settlement*`), `+`/`-`/`*`/`/`/`%`, comparisons and booleans,
  `div_ceil`, `checked_`/`wrapping_` add, sub and mul, `checked_` div and rem,
  `saturating_` add and sub, `then_some`, built-in derives and `#[cfg(test)]`
  modules.
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
python3 scripts/make-family.py /tmp/security-family   # generates all 4 pairs (or pass --problem <name>)

# Oracle (reference) runs; Harbor builds the agent and the separate verifier image.
for p in authorization settlement settlement-modular settlement-engine; do
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
correct and incorrect Rust repairs across both families, hostile Lean, sandbox
isolation, independent scoring, all 8 reference tasks):

```bash
docker build -t security-verifier:v3-review -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3-review python3 /repo/scripts/selftest.py   # ends with "selftest v3: PASS"
```

If Docker runs on another host, put Harbor's jobs directory on a filesystem
shared with that host, because verifier logs are bind-mounted.

## Evidence and baseline status

- **References:** `evidence/v3/` records Harbor 0.9.0 oracle runs with 1.00 on
  both tasks, plus the selftest pass. Those runs used commit `11489ee`, whose
  prompt SHA-256 is `24406f25…`. Later commits only reworded `instruction.md`
  and added the `settlement` task pairs.
- **GLM 5.3 Flash (`authorization`):** fresh Harbor 0.9.0 runs with `terminus-2` and
  `zai/glm-5.3-flash` scored **1.00 on each `authorization` v3 task** (mean 1.00). Both trials
  passed all four checkpoints: spec 0.25, verdict 0.15, proof 0.25 and response
  0.35. Complete trajectories, terminal recordings, submitted artifacts and
  verifier reports are in `evidence/v3/glm-5.3-flash/`.
- **Claude Opus 5.5 & GPT 6.1 Sol (`high`) across the 3 `settlement` isolation levels:**
  fresh Harbor 0.9.0 runs via `sandboxed.sh` (`terminus-2`, `reasoning_effort=high`, `max_turns=25`)
  evaluated both models on all six `settlement*` tasks (`settlement`, `settlement-modular`,
  and `settlement-engine` in both `vulnerable` and `safe` variants). Complete trajectories,
  terminal recordings, submitted artifacts and verifier reports are in
  `evidence/v3/claude-opus-5-5/` and `evidence/v3/gpt-6.1-sol-high/`:

| Task | Isolation level | Model | Reward | Episodes | Input / Output tokens |
|---|---|---|---:|---:|---:|
| `settlement-vulnerable` | Level 0 — Isolated | `claude-opus-5-5` | **1.00** | 11 | 125,566 / 13,927 |
| `settlement-safe` | Level 0 — Isolated | `claude-opus-5-5` | **1.00** | 13 | 204,438 / 26,781 |
| `settlement-modular-vulnerable` | Level 1 — Modular (4 modules) | `claude-opus-5-5` | **1.00** | 7 | 82,393 / 13,037 |
| `settlement-modular-safe` | Level 1 — Modular (4 modules) | `claude-opus-5-5` | **1.00** | 15 | 291,454 / 17,616 |
| `settlement-engine-vulnerable` | Level 2 — Engine + noise (6 modules) | `claude-opus-5-5` | **1.00** | 12 | 203,563 / 14,746 |
| `settlement-engine-safe` | Level 2 — Engine + noise (6 modules) | `claude-opus-5-5` | **1.00** | 20 | 326,168 / 28,548 |
| `settlement-vulnerable` | Level 0 — Isolated | `gpt-6.1-sol` (`high`) | **1.00** | 11 | 85,546 / 4,823 |
| `settlement-safe` | Level 0 — Isolated | `gpt-6.1-sol` (`high`) | **1.00** | 19 | 222,260 / 6,129 |
| `settlement-modular-vulnerable` | Level 1 — Modular (4 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 11 | 100,604 / 4,862 |
| `settlement-modular-safe` | Level 1 — Modular (4 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 25 | 512,074 / 7,345 |
| `settlement-engine-vulnerable` | Level 2 — Engine + noise (6 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 12 | 141,956 / 4,373 |
| `settlement-engine-safe` | Level 2 — Engine + noise (6 modules) | `gpt-6.1-sol` (`high`) | **1.00** | 25 | 574,267 / 7,982 |

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
scripts/make-family.py          generates all 4 symmetric task pairs (8 Harbor tasks)
scripts/references/             authorization-safe reference proof
scripts/selftest.py             adversarial regression suite covering all 4 task pairs
scripts/harbor-smoke.py         Harbor E2E check of reference task pairs
evidence/v3/                    current-version validation; other evidence/ entries are v1/v2
evidence/v3/glm-5.3-flash       complete GLM 5.3 Flash v3 Harbor runs and traces
evidence/v3/claude-opus-5-5     complete Claude Opus 5.5 v3 Harbor runs and traces across settlement*
evidence/v3/gpt-6.1-sol-high    complete GPT 6.1 Sol (high) v3 Harbor runs and traces across settlement*
```

