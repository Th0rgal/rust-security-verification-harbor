FROM rust:1.85-bookworm
COPY workspace/ /workspace/
WORKDIR /workspace
RUN cd challenge && cargo test --release && mkdir -p /workspace/submission/src
