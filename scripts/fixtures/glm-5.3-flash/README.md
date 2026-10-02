# Original GLM artifact replay

These are byte-for-byte artifacts from the real GLM 5.3 Flash snapshot at
`/var/lib/sandboxed-node/work/dcee3b3c-b23e-4881-8ba5-56a380f2a73f/glm-artifact-snapshot`.
`original-SHA256SUMS` preserves the recorded original paths and hashes. Selftest
maps those paths to this fixture and rejects drift. The source snapshot was
independently read and hashed again during v2 validation; all four hashes match.
The v1 verifier logs are retained in `v1-results/` (score 0.00 due to cascade).

Under v2: spec 0.10 (safety and explicit overflow, no successful output or iff
contract), witness 0.25, repair 0.25, proof 0.00, total **0.60**. The existing proof
attempts to unfold an `authorize` identifier that the opaque API does not expose;
it fails the exact submitted theorem. No artifact was adapted to make it pass.
See `evidence/glm-v2-details.json` and the Harbor replay evidence for diagnostics.
