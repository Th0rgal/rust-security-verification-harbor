# Rust authorization audit: a Lean-native, symmetric Harbor benchmark

Two Harbor tasks ask an agent to specify a small Rust authorization function in
Lean, decide whether it conforms to its documented policy over the full `u64`
domain, and justify that decision.
The two tasks receive byte-identical instructions. One implementation is
vulnerable to integer overflow (CWE-190); the other is correct. A fixed verdict
therefore cannot score well on both.

## Provenance

- Authored by LFG Labs (MIT, see [LICENSE](LICENSE)). The Rust function is a
  purpose-written benchmark exercise, not code extracted from an upstream
  repository. No CVE inspired or corresponds to it; CWE-190 is its weakness
  classification, not a provenance claim.
- `task/` is the single source tree and defines the **vulnerable** task.
  `scripts/make-family.py` derives both tasks from it and asserts that their
  `instruction.md` files are byte-identical.
- Toolchains are pinned. Lean is `leanprover/lean4:v4.31.0` and Z3 is
  `z3-solver==4.13.3.0`. Rust is `rust:1.85-bookworm`, and Lean ships in
  `ghcr.io/lfglabs-dev/rvb-lean-deps`; both are pinned by digest in the
  Dockerfiles. Harbor is `harbor==0.9.0`, pinned in
  `scripts/harbor-requirements.lock`.
- This is benchmark version 3 (`track = "lean-native-symmetric-v3"`). Versions 1
  and 2 graded a JSON specification DSL against the vulnerable program only. Their code, fixtures and
  evidence remain for reproducibility in `scripts/archive/`, `scripts/fixtures/`
  and `evidence/` (outside `evidence/v3/`), but they are not v3 results.

## The two variants

| Task | `authorize` computes `total` as | Visible Lean model | Expected verdict |
|---|---|---|---|
| `lfglabs/authorization-vulnerable` | `amount.wrapping_add(fee)` | `UInt64` (wrapping) addition | `.vulnerable` |
| `lfglabs/authorization-safe` | `amount.checked_add(fee)?` | `Nat` sum, rejected if `≥ 2^64` | `.safe` |

Everything else in the prompt and API is shared, including the tests. Apart from
the task name, only four things differ: the original Rust, its visible Lean
model (`SecurityChallenge.challengeAuthorize`), the reference solution and the
verifier's trusted `variant.txt`. For example,
`(balance, amount, fee) = (0, 2^64-1, 1)` makes the vulnerable code authorize a
debit of `0`.

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
  truncated `-`, `=`, `<`, `≤`, `∧`, `∨`, `¬`, `↔`, non-dependent `→` and
  non-dependent `if`.
- **Unsupported:** `UInt64` arithmetic, quantifiers, recursors and other heads.
  These yield `unsupported` for the affected facets, not "wrong". There is no
  fallback for arbitrary Lean. `unknown` and `timeout` (10 s per query) earn no
  credit.

The hidden contract is `accept ⇔ amount + fee ≤ balance`, computed in unbounded
integers, with `totalDebit = amount + fee` on acceptance. Because `balance` is a
`u64`, this also rules out overflow. The spec has four equally weighted facets:

1. **Safety:** `accepts → amount + fee ≤ balance`.
2. **Completeness:** `amount + fee ≤ balance → accepts`.
3. **Output exactness:** on accepted inputs, every allowed output equals
   `amount + fee`, and the output is unique. This facet also requires facet 4.
4. **Existence/coherence:** `accepts` is satisfiable, and every accepted input has
   some `u64` output.

So an all-`False` spec earns only facet 1, which is 6.25 of 100 points.

### Rust grading

`rust_symbolic.py` parses a documented subset of Rust and proves, with Z3 over all
`u64` inputs, that `Some` holds iff `amount + fee ≤ balance` and that
`total_debit = amount + fee`.

- **Supported subset:** `let` and shadowing, `if`/`else`, `if let`, exhaustive
  `Option` matches, `return`, `?`, casts, `+`/`-`, comparisons and booleans,
  `checked_`/`wrapping_` add and sub, `saturating_add`, `then_some`,
  built-in derives and `#[cfg(test)]` modules.
- **Rejected before execution:** loops, macros, helper functions, `unsafe`,
  crate attributes and dependencies.

The code is then compiled (`rustc -O`, overflow checks off) and run on 266+
concrete cases, including any SMT counterexample. A witness passes only if the
verifier's own pristine build authorizes the unaffordable triple with the
wrapped total.

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
python3 scripts/make-family.py /tmp/authorization-family   # refuses to overwrite

# Oracle (reference) runs; Harbor builds the agent and the separate verifier image.
for v in vulnerable safe; do
  .venv/bin/harbor run -p /tmp/authorization-family/authorization-$v -a oracle -e docker -n 1
done
```

To evaluate a model, replace `-a oracle` with any Harbor agent and model, for
example `-a terminus-2 -m <model>`. Run **both** tasks and report each reward,
along with the mean. If you pin `docker_image` in `task.toml`, use the
task-specific image for each variant, because the two variants' images differ.

Reference end-to-end check, which builds fresh images, runs both oracles, asserts
1.00 and identical prompts, and checks artifact hashes after Harbor's copy:

```bash
.venv/bin/python scripts/harbor-smoke.py --harbor .venv/bin/harbor --output /tmp/v3-e2e
```

Adversarial regression suite (equivalent/weak/vacuous/unsupported specs, 11
correct and 6 incorrect Rust repairs, hostile Lean, sandbox isolation,
independent scoring, both references):

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
  (current SHA-256 `9ebb3742…`) and documentation; the verifier and task
  artifacts are unchanged.
- **GLM 5.3 Flash: no v3 baseline exists.** The only GLM submission came from
  Harbor's `terminus-2` agent on the original **v1** task, where it scored 0.00.
  The same unmodified artifacts were replayed under v2 JSON grading and scored
  **0.60**: spec 0.10, witness 0.25, repair 0.25, proof 0.00. This was a regrade,
  not a new model run; the artifact SHA-256s are pinned in
  `scripts/fixtures/glm-5.3-flash/`.
  That 0.60 measures a different interface and must not be quoted as a v3
  score. A v3 baseline requires new runs on both tasks.

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
task/                     vulnerable task source (instruction, environment, tests/verifier, solution)
scripts/make-family.py    generates authorization-{vulnerable,safe}
scripts/references/       safe-variant reference proof
scripts/selftest.py       adversarial regression suite
scripts/harbor-smoke.py   Harbor E2E check of both references
evidence/v3/              current-version validation; other evidence/ entries are v1/v2
```
