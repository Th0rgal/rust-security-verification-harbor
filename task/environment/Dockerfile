ARG LEAN_BASE=ghcr.io/lfglabs-dev/rvb-lean-deps@sha256:a31dc0e4b707a3f419cdfa34af1ba5c5f7d147a401caad720e2e5b17cc3293e2
FROM ${LEAN_BASE} AS lean
FROM rust:1.85-bookworm@sha256:e51d0265072d2d9d5d320f6a44dde6b9ef13653b035098febd68cce8fa7c0bc4
RUN apt-get update && apt-get install -y --no-install-recommends python3 tmux asciinema libseccomp2 \
 && rm -rf /var/lib/apt/lists/*
COPY --from=lean /opt/lean/ /opt/lean/
ENV PATH="/opt/lean/bin:${PATH}" LEAN_PATH=/workspace/lean
COPY workspace/ /workspace/
WORKDIR /workspace
RUN cd challenge && cargo test --release && mkdir -p /workspace/submission/src \
 && cd /workspace/lean && lean Signature.lean
