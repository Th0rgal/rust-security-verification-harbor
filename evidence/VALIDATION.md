# Validation receipts

The WIP branch `semantic-grader-v2` was copied with its uncommitted changes from
`/var/lib/sandboxed-node/work/11c372f6-936b-4b2f-9ab6-f2a7c068fee3/rust-security-verification-harbor`
into this mission's independent workspace. The original worktree was not edited.
Base commit: `7808fc0` (Preinstall Terminus runtime dependencies).

- `selftest.log`: adversarial specs, independent facets, unsupported and incorrect
  Rust, the signed-literal inference regression, pristine witnesses, hostile Lean
  terms, kernel/axiom audits, symlink/size checks, immutable GLM replay and discovery
  leakage checks. Executed in `security-verifier:v2` with runtime network disabled,
  a read-only repository mount and `VERIFIER_ROOT=/opt/security-verifier`.
- `glm-v2-details.json`: immutable real GLM snapshot replay, full facets/checks,
  exact artifact hashes and failing Lean diagnostic; total 0.60.
- `rust-inference-regression.log`: old backend's false positive reproduced against
  actual compiled Rust, followed by final backend's explicit unsupported verdict.
  The rare signed-literal path now receives no patch credit.
- `harbor-smoke.log`, `harbor/summary.json`, `harbor/*-details.json`: Harbor 0.9.0
  oracle trials in offline separate Docker environments. Reference 1.00, GLM 0.60;
  specify/refute/repair/prove reference 1.00 each; focused GLM spec 0.50.
  Artifact SHA-256 values are checked after Harbor copies artifacts. The discovery
  image is built and checked to contain neither `/workspace/lean` nor a Lean binary.
- `api-clean-build.log`, `api-rebuild.log`: trusted API and ProofAudit rebuilt
  without cache; both compiled hashes match the tested verifier image
  (`API-SHA256SUMS`). The opaque API is also byte-compared
  against the committed .olean (SHA-256
  `761297c8b5e59462e8a06595bb22f52d047c6521d799cde45a5b63eec0aa8230`).
- `agent-build.log`, `verifier-build.log`: actual image builds; IDs used for Harbor
  are in its summary. `runtime.json` records actual versions and Landlock support.
- `local-proof.log`: reference proof checked through the agent's local Lean helper
  (exit 0; successful Lean produces no stdout).

The exact source GLM snapshot was read and hashed independently on this host.
The four digests match `scripts/fixtures/glm-5.3-flash/original-SHA256SUMS`.
The snapshot's v1 results are retained unchanged. This is artifact replay, not
an additional model evaluation.

Docker Compose v2.39.4 was installed for this mission after the host's missing
Compose plugin blocked Harbor startup. The downloaded linux-x86_64 binary matched
the release SHA-256
`7af95166a730b87e172d4fc9aefea8725d3c6c7327d59149267b452114ddb7d4`.
Earlier failed attempts (missing Compose, prebuilt tag deletion, and focused
weights missing from prebuilt test.sh) were diagnosed and corrected before the
recorded final suite. Their raw output remains outside the repository under
`/tmp/security-harbor-*`; the committed receipts describe the final implementation.

See BACKEND.md for reproducible commands and the limits of the Rust subset,
parser/interpreter trust, separate Lean theorem, sandbox and image reproducibility.
No branch push or main update is part of this validation.

Committed text logs have carriage returns, ANSI color sequences and trailing
spaces normalized for readability. Verdicts and JSON artifact hashes are unchanged.
