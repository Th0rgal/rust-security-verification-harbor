# Semantic grader v2

## Reward and specification contract

Four checkpoints are independent: spec 0.20, pristine witness 0.25, Rust repair
0.25, Lean proof 0.30. A missing/invalid spec never locks another checkpoint.
`details.json` records status, per-artifact SHA-256, checks and exact credit.
`partial` is an explicit spec status; `passed` means the entire checkpoint passed.

The spec checkpoint has four equal facets, worth 0.05 each in the integrated
task (0.25 each in the focused specify task):

| Facet | Required evidence |
|---|---|
| Affordability/safety | Nonempty acceptance and no accepted mathematical total above balance |
| Exact `total_debit` | Explicit unsigned output expression, universally equal to `amount + fee` on accepted inputs |
| Explicit overflow | Explicit `on_overflow: "reject"` clause and no accepted mathematical sum above `u64::MAX` |
| Completeness | Explicit `completeness: "iff"` clause and acceptance equivalent to reference acceptance on all u64 inputs |

All facets require non-vacuity. A safe but strict predicate can earn safety,
output and overflow credit, while failing reference validity and completeness.
Facets are independently assessed; e.g. a correct output clause does not fix
unsafe acceptance. Syntax/type errors earn zero specification credit.

`accept` describes acceptance only. The fact that
`amount + fee <= balance` is equivalent to the reference acceptance predicate
**does not express the successful output or assert an iff contract**. Mathematical
arithmetic and u64 input bounds imply overflow exclusion here, but do not count
as an *explicit* overflow clause. Missing clauses stay missing.

The historical `{property, arithmetic, on_overflow}` adapter recognizes only
the two historical property spellings. It contributes affordability/safety and
explicit overflow rejection, never an output clause or completeness. It is not
advertised in discovery prompts/schema. The immutable real GLM fixture has this
partial legacy spec, a valid overflow witness, a correct checked-add patch, and
a failing Lean term: **0.10 + 0.25 + 0.25 + 0.00 = 0.60**. Its four SHA-256 values
match the original snapshot. This regrades stored artifacts; it is not a new
GLM run. The v1 reward of 0.00 resulted from its spec gate and cascade locks.

DSL v2 has `version:2`, required Boolean `accept`, and optional unsigned
`total_debit`, `on_overflow`, `completeness`. Expressions support input names,
unsigned constants, mathematical add, comparisons and Boolean connectives.
The verifier enforces types, 64 nodes across both expressions, depth 12, u128
constants, duplicate-key rejection and 64 KiB artifact limits. Queries use
mathematical integers constrained to the *entire* u64 input domain, Z3
4.13.3.0, seed 0, and a 10-second limit **per query**. `unsat` proves a universal
check in this encoding; `sat` records a concrete counterexample. `unknown` and
`timeout` never earn credit for the affected check. Version mismatch is an
infrastructure error, not a passing check.

## Rust correspondence and limits

The verifier parses a closed production subset before compiling or executing
submitted Rust. Only the public `Authorization { total_debit: u64 }` and
three-u64 `authorize` returning `Option<Authorization>` are accepted. Built-in
derives and top-level `#[cfg(test)] mod ...` are allowed; the latter are absent
from production compilation. Extra production declarations, user attributes,
macros, dependencies, unsafe, loops and helper calls are unsupported.

Immutable lets and shadowing, blocks, returns, conditionals, exhaustive Option
matches, if-let, `?`, integer casts, unsigned arithmetic/comparisons, short-circuit
Boolean operators, checked/wrapping add/sub, saturating add, then_some and exact
Authorization construction are interpreted as path guards and typed values.
Two unsuffixed integer operands are unsupported: Rust can infer i32 for a
context-free `1 - 2`, and treating it as u64 would be unsound. This includes a
regression whose rare trigger is replayed in actual Rust and rejected by the
final backend before grading. Integer values use mathematical integers; release u64/u128 add/sub and narrowing
casts use modular arithmetic. Checked operations split Some/None paths; then_some
evaluates its argument eagerly and Boolean connectives short-circuit. Unresolved
literal types, unsupported ASTs and expansion beyond limits fail closed.

For every path, SMT checks Some iff mathematical total is affordable, exact
successful `total_debit`, and complete path coverage. Because balance is u64,
affordable implies the total is representable. Rust is compiled by pinned
rustc 1.85.1, edition 2021, optimized with overflow checks explicitly off. A
separate driver checks API types and 266 deterministic boundary/random cases;
SMT counterexamples are also replayed in compiled Rust. Concrete sampling
cannot grant patch credit without universal success.

This is **not a machine-checked proof of the Python parser/interpreter, rustc,
LLVM, or Z3**. Universal equivalence holds within the implemented subset and
its correspondence assumptions. Differential/adversarial tests exercise those
assumptions, including rare triggers invisible to the base sample. Unsupported
correct Rust can receive zero credit; the grader never substitutes sampling
for unsupported semantics. SMT resource limits can reject a correct patch.

The witness runs independently against verifier-owned pristine release Rust.
It must observe Some for a mathematically unaffordable total. Editing the
agent-visible challenge has no effect. Input JSON must contain exactly three
u64 decimal integer values; booleans, fractions and duplicate keys are rejected.

## Lean proof and isolation

The agent receives a compiled opaque `SecurityChallenge` API, a signature and
its success characterization in integrated/prove tasks. The API is rebuilt from
a trusted source with Lean 4.31.0 and no external Lake dependencies. A private
opaque certified function carries a kernel-checked success contract. The exact
submitted theorem has Nat arguments and concludes exact mathematical output
and affordability from API success. It does **not** prove the submitted Rust,
completeness, or a Rust-to-Lean translation. Rust equivalence is checked separately.

Proof terms do not need any particular tactic. Only SecurityChallenge, Lean,
Std and Lean.Elab.Tactic.Omega imports are accepted. The verifier rejects obvious
declaration/axiom escapes, sorry and native_decide; this lexical check is not
the trust boundary. Elaboration runs with Landlock filesystem restrictions,
seccomp, dropped root credentials, resource limits and a process-group deadline.
Candidate output is frozen; other temporary files are removed before replay.
`leanchecker` independently checks the serialized module. The trusted,
precompiled `ProofAudit` loads Candidate as data, checks the exact theorem type
and recursively audits dependencies for axioms. Only propext, Classical.choice
and Quot.sound are allowed. Missing sandbox/toolchain/API is an infrastructure
error; no unsandboxed fallback is provided.

Tests include sorry/admit/new axioms, forbidden imports, wrong types,
declaration escapes, injected tactic-side axioms and attempted writes outside
the temporary proof directory. This protects against the tested metaprogram
attacks, not arbitrary kernel vulnerabilities or a hostile container host.
Linux Landlock and libseccomp are mandatory; filesystem isolation does not
claim complete side-channel isolation. Compilation and proof checks have finite
limits; overall Harbor verification is limited to 1200 seconds and 4 GiB.

## Discovery tracks

`scripts/make-family.py OUTPUT` generates integrated/specify/refute/repair/prove
tasks from the shared verifier. The trusted `[verifier].env.GRADER_PROFILE`
selects weights through the shared `test.sh`, including with prebuilt images. Specify and refute expose only their discovery
instructions, vulnerable Rust and neutral DSL grammar. Their images have no
Lean toolchain/API/signature or proof skeleton; they do not ship a canonical
spec example, repaired implementation, or repair instructions. The intended
service policy in the vulnerable source remains available for discovery.
Solutions and trusted verifier files are outside the agent image. Integrated
and prove deliberately expose the proof contract and should not be used to
measure unguided invariant discovery.

## Reproduce

Prerequisites: Linux x86_64 with Landlock, Docker Engine, Docker Compose v2,
Python 3.12 and access to the pinned ghcr.io Lean dependency image. Build-time
network access is required for apt/pip; agent and verifier runtime are offline.
Both base images are pinned by digest in Dockerfiles. Lean 4.31.0, Rust 1.85.1,
Z3 4.13.3.0 and Harbor 0.9.0 are fixed. The host Harbor Python dependency lock
is `scripts/harbor-requirements.lock`.

```bash
python3 -m venv .venv
.venv/bin/pip install -r scripts/harbor-requirements.lock
scripts/build-lean-api.sh --check
# Omit --check only when intentionally regenerating the committed opaque API.
docker build -t security-agent:v2 -f task/environment/Dockerfile task/environment
docker build -t security-verifier:v2 -f task/tests/Dockerfile task/tests
mkdir -p /tmp/security-evidence
docker run --rm --network none --security-opt no-new-privileges \
  -v "$PWD:/repo:ro" -v /tmp/security-evidence:/evidence \
  -e VERIFIER_ROOT=/opt/security-verifier \
  -e GLM_DETAILS_OUT=/evidence/glm-v2-details.json \
  security-verifier:v2 python3 -u /repo/scripts/selftest.py
.venv/bin/python scripts/harbor-smoke.py --harbor "$PWD/.venv/bin/harbor" \
  --output /tmp/security-evidence/harbor
python3 scripts/make-family.py /tmp/security-family
```

Use fresh output directories. The selftest rejects immutable GLM fixture hash
drift, checks reference 1.00, skeleton 0.00, independent later credit 0.80 and
GLM 0.60. Harbor smoke tests the oracle reference, four focused references, focused GLM
spec 0.50, and verbatim integrated GLM artifacts
through separate Docker agent/verifier environments, including artifact copy.
The API rebuild is byte-compared to the committed .olean. Evidence records
actual image IDs, tool versions, reference/GLM verdicts and test logs.

Reproducibility here means fixed solver inputs, reference artifacts, toolchain
and score, not byte-identical entire container images: apt repositories and
installation metadata are not frozen. Rebuilding base-derived runtime images
may produce different IDs. The committed API is reproducibly checked, and
runtime images used for the reported validation are identified in evidence.
