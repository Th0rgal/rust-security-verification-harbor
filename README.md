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

## CTRL-G / external evaluation

Requirements: Docker, Python 3.12+, x86_64 Linux, Harbor 0.9.0 and roughly
10 GB of free disk. The task is self-contained and the verifier runs offline.

```bash
git clone https://github.com/Th0rgal/rust-security-verification-harbor.git
cd rust-security-verification-harbor
python3 -m venv .venv
.venv/bin/pip install -r scripts/harbor-requirements.lock

# Rebuild locally (authoritative and reproducible path).
docker build -t rust-security-overflow-agent:v2 \
  -f task/environment/Dockerfile task/environment
docker build -t rust-security-overflow-verifier:v2 \
  -f task/tests/Dockerfile task/tests

# Validate the reference, immutable GLM replay and focused task family.
.venv/bin/python scripts/harbor-smoke.py \
  --harbor "$PWD/.venv/bin/harbor" \
  --agent-image rust-security-overflow-agent:v2 \
  --verifier-image rust-security-overflow-verifier:v2 \
  --output /tmp/rust-security-overflow-results
```

Prebuilt amd64 images are also published for quick testing. If GHCR requests
authentication, use a GitHub token with `read:packages`:

```bash
echo <TOKEN> | docker login ghcr.io -u <GITHUB_USER> --password-stdin
docker pull ghcr.io/th0rgal/rust-security-overflow-agent@sha256:50367933d7c10fae2f7eb88837f33d9169496a623a1938e8dc0467391e567d85
docker pull ghcr.io/th0rgal/rust-security-overflow-verifier@sha256:22fc68e9f8ca662a7984834aaedcea2dc9627072a216a0d9f81fa71010e8aad6
docker tag ghcr.io/th0rgal/rust-security-overflow-agent@sha256:50367933d7c10fae2f7eb88837f33d9169496a623a1938e8dc0467391e567d85 security-agent:v2
docker tag ghcr.io/th0rgal/rust-security-overflow-verifier@sha256:22fc68e9f8ca662a7984834aaedcea2dc9627072a216a0d9f81fa71010e8aad6 security-verifier:v2
.venv/bin/python scripts/harbor-smoke.py --harbor "$PWD/.venv/bin/harbor"
```

To test another Harbor-compatible agent/model on the integrated task:

```bash
harbor run -p task -a <agent> -m <model> -e docker
```

To benchmark one capability at a time, generate `integrated`, `specify`,
`refute`, `repair` and `prove` tasks and point Harbor at the generated folder:

```bash
python3 scripts/make-family.py /tmp/rust-security-overflow-family
harbor run -p /tmp/rust-security-overflow-family -a <agent> -m <model> -e docker
```

Expected control scores are reference `1.00`, empty skeleton `0.00`, and the
immutable GLM 5.3 Flash artifact replay `0.60`. See `evidence/VALIDATION.md` and
`evidence/harbor/summary.json` for machine-readable evidence.
