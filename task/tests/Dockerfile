ARG LEAN_BASE=ghcr.io/lfglabs-dev/rvb-lean-deps@sha256:a31dc0e4b707a3f419cdfa34af1ba5c5f7d147a401caad720e2e5b17cc3293e2
FROM rust:1.85-bookworm@sha256:e51d0265072d2d9d5d320f6a44dde6b9ef13653b035098febd68cce8fa7c0bc4 AS rust
FROM ${LEAN_BASE} AS api
COPY verifier/SecurityChallenge.lean verifier/ProofAudit.lean verifier/lakefile.lean verifier/lake-manifest.json verifier/lean-toolchain /build-api/
WORKDIR /build-api
RUN lake build SecurityChallenge ProofAudit

FROM ${LEAN_BASE}
COPY --from=rust /usr/local/rustup /usr/local/rustup
COPY --from=rust /usr/local/cargo /usr/local/cargo
ENV PATH="/usr/local/cargo/bin:${PATH}" RUSTUP_HOME=/usr/local/rustup CARGO_HOME=/usr/local/cargo
RUN python3 -c "import shutil; shutil.rmtree('/opt/security-verifier', ignore_errors=True)"
COPY verifier/*.py verifier/requirements.txt /opt/security-verifier/
COPY verifier/pristine/ /opt/security-verifier/pristine/
COPY --from=api /build-api/.lake/build/lib/lean/SecurityChallenge.olean /opt/security-verifier/api/SecurityChallenge.olean
COPY --from=api /build-api/.lake/build/lib/lean/ProofAudit.olean /opt/security-verifier/api/ProofAudit.olean
COPY verifier/ProofAudit.lean /opt/security-verifier/ProofAudit.lean
COPY test.sh /tests/test.sh
RUN apt-get update && apt-get install -y --no-install-recommends gcc libc6-dev libseccomp2 \
 && python3 -m pip install --break-system-packages --no-cache-dir -r /opt/security-verifier/requirements.txt \
 && chmod 0555 /tests/test.sh && mkdir -p /workspace/submission/src /logs/verifier
WORKDIR /workspace
