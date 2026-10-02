FROM rust:1.85-bookworm AS rust
FROM ghcr.io/lfglabs-dev/rvb-lean-deps@sha256:a31dc0e4b707a3f419cdfa34af1ba5c5f7d147a401caad720e2e5b17cc3293e2
COPY --from=rust /usr/local/rustup /usr/local/rustup
COPY --from=rust /usr/local/cargo /usr/local/cargo
ENV PATH="/usr/local/cargo/bin:${PATH}" RUSTUP_HOME=/usr/local/rustup CARGO_HOME=/usr/local/cargo
COPY verifier/ /opt/security-verifier/
COPY test.sh /tests/test.sh
RUN chmod 0555 /tests/test.sh && mkdir -p /workspace/submission/src /logs/verifier \
 && cd /opt/security-verifier && mkdir -p .lake && ln -s /opt/rvb-deps/packages .lake/packages \
 && lake build SecurityChallenge
WORKDIR /workspace
