#!/usr/bin/env bash
set -u
mkdir -p /logs/verifier
exec python3 /opt/security-verifier/verify.py \
  --profile "${GRADER_PROFILE:-integrated}" --workspace /workspace \
  --verifier /opt/security-verifier \
  --logs /logs/verifier
