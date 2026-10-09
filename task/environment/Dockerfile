ARG LEAN_BASE=ghcr.io/lfglabs-dev/rvb-lean-deps@sha256:a31dc0e4b707a3f419cdfa34af1ba5c5f7d147a401caad720e2e5b17cc3293e2
FROM rust:1.85-bookworm@sha256:e51d0265072d2d9d5d320f6a44dde6b9ef13653b035098febd68cce8fa7c0bc4 AS rust
FROM ${LEAN_BASE}
COPY --from=rust /usr/local/rustup /usr/local/rustup
COPY --from=rust /usr/local/cargo /usr/local/cargo
ENV PATH="/opt/lean/bin:/usr/local/cargo/bin:${PATH}" RUSTUP_HOME=/usr/local/rustup CARGO_HOME=/usr/local/cargo LEAN_PATH="/workspace/lean:/opt/rvb-deps/packages/mathlib/.lake/build/lib/lean:/opt/rvb-deps/packages/batteries/.lake/build/lib/lean:/opt/rvb-deps/packages/aesop/.lake/build/lib/lean:/opt/rvb-deps/packages/Qq/.lake/build/lib/lean:/opt/rvb-deps/packages/proofwidgets/.lake/build/lib/lean:/opt/rvb-deps/packages/plausible/.lake/build/lib/lean:/opt/rvb-deps/packages/importGraph/.lake/build/lib/lean:/opt/rvb-deps/packages/LeanSearchClient/.lake/build/lib/lean:/opt/rvb-deps/packages/hax/.lake/build/lib/lean"
RUN apt-get update && apt-get install -y --no-install-recommends python3 tmux asciinema libseccomp2 gcc libc6-dev \
 && rm -rf /var/lib/apt/lists/*
COPY workspace/ /workspace/
WORKDIR /workspace
RUN cd /workspace/lean \
 && if [ -d LeanModel ]; then \
      for m in Constants WordMath ReciprocalDiv BroadwordSwar MontgomeryField GoldilocksField FeeSchedule LiquidityPool TranscriptCodec ClearingPipeline; do \
        if [ -f "LeanModel/${m}.lean" ]; then lean -o "LeanModel/${m}.olean" "LeanModel/${m}.lean"; fi; \
      done; \
    fi \
 && lean -o SecurityChallenge.olean SecurityChallenge.lean \
 && cd /workspace/challenge && cargo test --release && mkdir -p /workspace/submission/src /workspace/submission/LeanModel \
 && cd /workspace/lean && lean Signature.lean
