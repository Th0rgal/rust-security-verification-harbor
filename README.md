# Rust authorization: Lean-native symmetric benchmark

Two Harbor tasks ask the same question with byte-identical instructions. One
implementation uses wrapping addition; the other uses checked addition. The
agent must infer and write a real Lean specification, decide whether the supplied
program conforms, and justify that decision. This is a local toy arithmetic
benchmark, not a claim of general Rust security.

The visible business requirements say that every affordable payment is
authorized, every unaffordable payment rejected, and the returned debit is the
principal plus fees actually applied by the wider-integer settlement layer.

## Agent outputs

- `Spec.lean`: a complete Lean module defining `candidateSpec : AuthorizationSpec`.
  Its `accepts` field takes balance, amount, fee; its `output` field also takes
  totalDebit. All arguments are `UInt64`, both fields return `Prop`.
- `Audit.lean`: a complete Lean module defining `verdict : AuditVerdict` as
  `.safe` or `.vulnerable`.
- `Proof.lean`: a proof term for `AuditClaim candidateSpec verdict`.
- For a vulnerable verdict: `counterexample.json` and repaired `src/lib.rs`.
  For a safe verdict these two artifacts must be absent.

The agent receives the original Rust, ordinary tests, the model of that original
program in `SecurityChallenge.lean`, and a local Lean compilation helper. The
reference policy and semantic checks live only in the separate offline verifier.

## What the score means

| Checkpoint | Weight | Evidence |
|---|---:|---|
| Lean specification | 25% | Four equally weighted semantic facets |
| Justified verdict | 15% | Correct decision; safe requires proof and universal original Rust check |
| Lean evidence | 25% | Kernel-checked `AuditClaim` of candidate spec and original model |
| Appropriate response | 35% | Vulnerable: witness 15%, universal patch 20%; safe: no unnecessary artifacts, proof and universal original Rust check |

The spec facets are safe acceptance (including overflow), completeness, exact
and unique output on accepted inputs, and existence/coherence. The last two
require a nonempty acceptance predicate and an output for every accepted input.
An all-False spec can earn only the safety facet (6.25 points out of 100).
Raw vacuous implications are visible in diagnostics but do not earn output credit.

Specs are elaborated by Lean; their serialized, kernel-replayed expressions are
converted to a typed arithmetic tree and checked by Z3 on the full u64 domain.
This intermediate JSON is generated internally by the trusted verifier; the
model writes Lean only. Text matching is never the semantic criterion.
Auxiliary definitions and equivalent expressions are accepted.

The translator currently supports input `UInt64.toNat`, Nat constants,
addition, truncated subtraction, comparisons/equality, propositional connectives,
nondependent implication, and `if`. Other valid Lean specs produce `unsupported`
for affected facets. There is no fallback for arbitrary Lean and no assertion
that unsupported means mathematically wrong. Timeouts/unknown do not earn credit.

Lean evidence concerns the **original visible model and submitted spec**.
It does not certify the repaired Rust, and the benchmark does not kernel-prove
the Rust-to-Lean translation. Original/repair Rust conformity to the hidden
business contract is a separate universal SMT analysis of a documented Rust
subset, backed by concrete compiled probes. See [BACKEND.md](BACKEND.md).

All scores are independent except the explicit justification required for a safe
decision. A malformed spec does not lock witness or repair scoring. A theorem
about a weak spec can earn Lean evidence while its spec facets fail; details name
that exact scope. Proofs can use any accepted kernel proof, not only `omega`.
Lean 4.31.0, independent replay, fixed theorem type and transitive axiom audit are
required. Allowed axioms: propext, Classical.choice, Quot.sound.

## CTRL-G / external evaluation

Build locally; previously published v2 images and the historic GLM 60% result
refer to the old JSON task and are **not v3 results**. No new GLM baseline is
claimed until the model runs again against both native Lean tasks.

```bash
git clone https://github.com/Th0rgal/rust-security-verification-harbor
cd rust-security-verification-harbor
python3 -m venv .venv
.venv/bin/pip install -r scripts/harbor-requirements.lock
python3 scripts/make-family.py /tmp/authorization-family

# Task-specific images: safe and vulnerable have different original Lean models.
for variant in vulnerable safe; do
  task_path="/tmp/authorization-family/authorization-$variant"
  docker build -t "authorization-agent:$variant-v3" -f "$task_path/environment/Dockerfile" "$task_path/environment"
  docker build -t "authorization-verifier:$variant-v3" -f "$task_path/tests/Dockerfile" "$task_path/tests"
done

# Oracle reference checks (Harbor builds the task-specific images).
.venv/bin/harbor run -p /tmp/authorization-family/authorization-vulnerable -a oracle -e docker -n 1
.venv/bin/harbor run -p /tmp/authorization-family/authorization-safe -a oracle -e docker -n 1
```

Use your usual CTRL-G Harbor agent in place of `oracle`. Runtime networking is
disabled. Keep the agent and verifier separate, and select matching task-specific
images if setting `docker_image` in task.toml. The verifier takes its variant and
original Rust from its own image, never from the agent environment.

Run the reproducible E2E helper with Docker Compose v2 installed:

```bash
.venv/bin/python scripts/harbor-smoke.py --harbor .venv/bin/harbor --output evidence/v3/e2e-check
```

For the full adversarial regression suite, install Lean 4.31.0 and Z3 4.13.3.0
(`task/tests/verifier/requirements.txt`), make the actual Lean toolchain binaries
available in PATH, build `lake build SecurityChallenge SpecAudit` in
`task/tests/verifier`, and run `python3 scripts/selftest.py`. Alternatively use
the pinned verifier Docker image with the repository mounted at `/repo` and
`VERIFIER_ROOT=/opt/security-verifier`. The suite covers equivalent Lean specs,
vacuity, invalid/unsupported specs, several Rust repairs, invalid proofs, sandbox
isolation, independent scores, both reference solutions and identical prompts.

The root-container regression command is:

```bash
docker build -t security-verifier:v3-review -f task/tests/Dockerfile task/tests
docker run --rm --network none -v "$PWD:/repo" \
  -e VERIFIER_ROOT=/opt/security-verifier \
  security-verifier:v3-review python3 /repo/scripts/selftest.py
```

`task/` is the shared source of the vulnerable task.
`scripts/make-family.py` materializes the two tasks without checking duplicated
generated trees into Git. Old JSON implementation and GLM fixtures are archived
under `scripts/archive` and `scripts/fixtures`; evidence outside `evidence/v3`
describes earlier benchmark versions.

If Docker runs on a separate host, choose a results directory on the shared
workspace filesystem, since Harbor mounts verifier logs directly into that path.
