#!/usr/bin/env bash
# Rebuild the opaque agent API and trusted precompiled auditor in pinned Docker.
set -euo pipefail
cd "$(dirname "$0")/.."
docker build --target api -t security-api:v2 -f task/tests/Dockerfile task/tests
api_container=$(docker create security-api:v2)
api_tmp=$(mktemp -d)
trap 'docker rm "$api_container" >/dev/null; rm -rf "$api_tmp"' EXIT
docker cp "$api_container:/build-api/.lake/build/lib/lean/SecurityChallenge.olean" "$api_tmp/SecurityChallenge.olean"
if [[ "${1:-}" == --check ]]; then
  cmp "$api_tmp/SecurityChallenge.olean" task/environment/workspace/lean/SecurityChallenge.olean
else
  cp "$api_tmp/SecurityChallenge.olean" task/environment/workspace/lean/SecurityChallenge.olean
fi
sha256sum task/environment/workspace/lean/SecurityChallenge.olean
