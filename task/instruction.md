# Security review: settlement authorization

Audit `/workspace/challenge`. Write the four artifacts under
`/workspace/submission`. The verifier uses its own pristine code and grades
**each artifact independently**: spec 0.20, witness 0.25, patch 0.25, proof 0.30.
Run `python3 /workspace/harness/checkpoint.py` for advisory hints and `READY`.

1. **Specify** in `spec.json`: typed DSL v2, an acceptance predicate on u64
   inputs with mathematical arithmetic. Recover the intended contract from the
   challenge. `spec.schema.json` defines types/operators and optional clauses
   `total_debit`, `on_overflow`, `completeness`. These four contract facets each
   earn 0.05: affordability/safety, exact successful output, explicit overflow
   rejection, and completeness. An acceptance predicate alone is partial.
   At most 64 nodes across all expressions, depth 12;
   constants 0..2^128-1. Spec checks separately test typing, non-vacuity,
   validity on reference, safety adequacy, and equivalence/completeness.
2. **Refute** in `counterexample.json`: exactly decimal JSON integer keys
   `balance`, `amount`, `fee`. Reproduce an authorization violating the
   mathematical policy against release-mode pristine vulnerable Rust.
3. **Repair** in `src/lib.rs`: preserve `Authorization { pub total_debit: u64 }`
   and `pub fn authorize(u64,u64,u64) -> Option<Authorization>`. Return the exact
   mathematical total iff amount plus fee is affordable. Overflow must fail.
   Equivalent checked addition, widened u128 arithmetic, or subtraction guards
   are accepted. No particular spelling is required. The exact symbolic backend
   supports immutable lets, if/else, if-let, exhaustive Option matches, returns,
   `?`, casts, +/-, comparisons/booleans, checked/wrapping add/sub,
   saturating_add, then_some, Some/None and Authorization construction.
   Built-in derives and top-level `#[cfg(test)] mod ...` are allowed.
   Other production items, macros, unsafe code, loops, helpers and dependencies
   are unsupported. There is no reward based solely on sampled tests.
4. **Prove** in `Proof.lean`: submit a proof term for the **exact** theorem in
   `/workspace/lean/Signature.lean`. The compiled opaque API and its success
   characterization are locally available. Run
   `python3 /workspace/lean/check.py` to check a candidate. The implementation
   source is hidden. Lean 4.31.0 checks the kernel proof; independent replay and
   a transitive axiom audit follow. No particular tactic is required.
   Imports allowed: SecurityChallenge, Lean, Std, Lean.Elab.Tactic.Omega.
   Axioms allowed: propext, Classical.choice, Quot.sound. No sorry, new axioms,
   declaration escapes, native_decide, unsafe/extern hooks or extra imports.

The Lean theorem concerns the certified mathematical API, with Nat arguments;
its score is independent of the Rust implementation, whose u64 equivalence is
checked separately. Empty, unsupported or failing artifacts never lock others.
