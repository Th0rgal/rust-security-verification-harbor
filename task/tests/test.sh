#!/usr/bin/env bash
set -u
mkdir -p /logs/verifier
exec python3 /opt/security-verifier/verify.py \
  --workspace /workspace \
  --verifier /opt/security-verifier \
  --logs /logs/verifier
