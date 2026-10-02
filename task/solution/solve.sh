#!/usr/bin/env bash
set -euo pipefail
for rel in Spec.lean Audit.lean Proof.lean counterexample.json src/lib.rs; do
  if [[ -f "/solution/$rel" ]]; then
    cp "/solution/$rel" "/workspace/submission/$rel"
  fi
done
