FROM rust:1.85-bookworm
RUN apt-get update && apt-get install -y --no-install-recommends python3 tmux asciinema \
 && rm -rf /var/lib/apt/lists/*
COPY workspace/ /workspace/
WORKDIR /workspace
RUN cd challenge && cargo test --release && mkdir -p /workspace/submission/src
