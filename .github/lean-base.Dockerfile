# Public, checksum-verified counterpart of the benchmark's registry Lean base.
FROM ubuntu:24.04@sha256:f610ab94648195aa356059f5b41d6085c9d4d903c072430cdd1af7bdb646106b
ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8 PATH="/opt/lean/bin:${PATH}"
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl zstd python3 python3-pip gcc libc6-dev libseccomp2 \
    && rm -rf /var/lib/apt/lists/*
RUN curl --fail --location --retry 3 \
      https://github.com/leanprover/lean4/releases/download/v4.31.0/lean-4.31.0-linux.tar.zst \
      -o /tmp/lean.tar.zst \
    && echo '07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f  /tmp/lean.tar.zst' | sha256sum --check \
    && mkdir -p /opt/lean \
    && tar --zstd -xf /tmp/lean.tar.zst --strip-components=1 -C /opt/lean \
    && rm /tmp/lean.tar.zst \
    && lean --version && leanchecker --help
