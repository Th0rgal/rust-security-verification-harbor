# Rust security verification Harbor

A settlement authorizer challenge with four independently graded artifacts:
semantic specification (0.20), pristine overflow witness (0.25), universally
checked Rust repair (0.25), and audited Lean proof (0.30).

Specification credit is split equally between affordability/safety, exact
`total_debit`, explicit overflow rejection and completeness. An acceptance
inequality alone earns partial credit. There are no cascade locks: a failed
spec cannot suppress a valid witness, repair or proof.

The Rust backend checks a bounded, typed production subset over the full u64
input domain using pinned Z3, then validates compiled Rust against concrete
cases. Lean checks an opaque certified mathematical API, with independent
kernel replay and transitive axiom audit; its proof is independent of Rust.

[BACKEND.md](BACKEND.md) describes the precise contract, scoring, trusted
components, supported subset, limitations and reproducible Docker/Harbor tests.
The immutable historical GLM snapshot scores **0.60** under v2; its spec is
partial and its proof fails. This is artifact replay, not a fresh model run.

```bash
# Install Harbor and dependencies as described in BACKEND.md, then build images.
scripts/build-lean-api.sh --check
docker build -t security-agent:v2 -f task/environment/Dockerfile task/environment
docker build -t security-verifier:v2 -f task/tests/Dockerfile task/tests
.venv/bin/python scripts/harbor-smoke.py --harbor "$PWD/.venv/bin/harbor" \
  --output /tmp/security-harbor-evidence
```

Generate focused tasks with `python3 scripts/make-family.py /tmp/security-family`.
Use **specify/refute** to measure discovery: they omit the repaired Lean contract,
proof skeleton and canonical answer examples. Integrated/prove expose the proof
API deliberately. For a model run use `harbor run -p <task> -a <agent> -m <model>
-e docker`; `task/task.toml` defines offline separate verification and artifacts.

The scenario is inspired by the
[Rust Verification Benchmark](https://github.com/lfglabs-dev/rust-verification-benchmark-harbor).
Its vulnerable code models release-mode wrapping before wider settlement.
Never deploy it.
