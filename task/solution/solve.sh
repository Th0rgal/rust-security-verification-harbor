#!/usr/bin/env bash
set -euo pipefail
for rel in Spec.lean Audit.lean Proof.lean counterexample.json src/lib.rs; do
  if [[ -f "/solution/$rel" ]]; then
    mkdir -p "$(dirname "/workspace/submission/$rel")"
    cp "/solution/$rel" "/workspace/submission/$rel"
  fi
done
if [[ -d "/solution/src" ]]; then
  mkdir -p /workspace/submission/src
  cp -r /solution/src/*.rs /workspace/submission/src/ 2>/dev/null || true
fi
if [[ -d "/solution/LeanModel" ]]; then
  mkdir -p /workspace/submission/LeanModel
  cp -r /solution/LeanModel/*.lean /workspace/submission/LeanModel/ 2>/dev/null || true
fi
