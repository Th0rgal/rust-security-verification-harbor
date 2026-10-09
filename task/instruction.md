# Specify and audit a Rust authorization crate

Audit `/workspace/challenge/src` for conformance with its documented
authorization policy over all `u64` inputs. The implementation may or may not
satisfy that policy; determine which from the code across all crate modules.
The ordinary tests are examples, not a complete specification.

The crate decides whether a payment or batch clearing settlement is authorized
before final commitment. Inputs (`balance`, `amount`, `fee`) and the output
`total_debit` field are `u64` values. Infer the intended mathematical behavior
from the crate's public API, module comments, and protocol invariants, including
boundary cases and rejection behavior. Every affordable transaction should be
authorized; every unaffordable transaction should be rejected. The authorization
reports the exact mathematical debit actually applied at settlement, consisting
of principal and all protocol fees/levies.

Submit to `/workspace/submission`:

1. `Spec.lean`: a complete Lean module defining
   `candidateSpec : SecurityChallenge.AuthorizationSpec`. Its fields are
   `accepts : UInt64 → UInt64 → UInt64 → Prop` and
   `output : UInt64 → UInt64 → UInt64 → UInt64 → Prop`, in argument order
   balance, amount, fee, then totalDebit for output. Define the intended policy,
   rather than merely copying the implementation. Auxiliary definitions and
   lemmas are welcome. Expressions are compared by meaning, never text.
2. `Audit.lean`: a complete Lean module defining
   `verdict : SecurityChallenge.AuditVerdict`, either `.vulnerable` or `.safe`.
   Here vulnerable means that at least one `u64` input triple violates the
   authorization policy; safe means conformity for every `u64` input triple.
3. `Proof.lean`: a Lean proof term for
   `SecurityChallenge.AuditClaim candidateSpec verdict`. The visible model and
   statement are in `/workspace/lean/SecurityChallenge.lean` (and, for
   multi-module crates, `/workspace/lean/LeanModel/*.lean`).
   - When `verdict` is `.safe`, this proves universal conformity of the original
     model (`Conforms candidateSpec challengeAuthorize`).
   - When `verdict` is `.vulnerable` on a multi-module crate with
     `/workspace/lean/LeanModel/`, `AuditClaim candidateSpec .vulnerable` is also
     universal conformity (`Conforms candidateSpec challengeAuthorize`) over your
     repaired Lean model submitted in `/workspace/submission/LeanModel/*.lean`
     (preserving fixed-width `UInt64` machine arithmetic; `Nat` is forbidden in
     `LeanModel/*.lean`).
   Use any kernel-checked proof, not just a particular tactic. Run
   `python3 /workspace/lean/check.py` for a local compilation check.
4. If your verdict is vulnerable, give:
   - `counterexample.json` with exactly decimal integer keys `balance`, `amount`,
     `fee` demonstrating an unaffordable input accepted by the original Rust code,
   - the repaired Rust module(s) in `/workspace/submission/src/` preserving the
     public API, and
   - (for multi-module crates with `/workspace/lean/LeanModel/`) the repaired
     Lean module(s) in `/workspace/submission/LeanModel/`.
   If safe, leave `counterexample.json`, `/workspace/submission/src/`, and
   `/workspace/submission/LeanModel/` absent; provide a universal proof instead
   of proposing an unnecessary repair.

The hidden verifier checks four independent specification facets: safe
acceptances, acceptance of all valid payments, exact/unique output on accepted
inputs, and existence of an output for every accepted input. Lean compilation,
independent kernel replay, type checks and a transitive axiom audit precede
semantic analysis. Spec grading uses a bounded translator of elaborated Lean
expressions to Z3: Nat constants, input UInt64.toNat, Nat +, truncated -,
*, constant /, %, constant-exponent ^, bitwise/shift operators, =, <, ≤,
And/Or/Not/Iff/implication, and nondependent if.
Auxiliary definitions are unfolded. Other expressions are reported unsupported,
not semantically false.
Imports allowed: SecurityChallenge, LeanModel, Lean, Std, Init, Mathlib, Batteries, Aesop, Qq (and submodules).
Axioms allowed: propext, Classical.choice, Quot.sound. No sorry, added axioms,
native_decide, unsafe/extern hooks or elaboration extensions.

Rust repairs are analyzed universally on the full u64 input domain within the
supported expression subset, then compiled and exercised concretely. Supported:
multi-file and inline modules, integer constants, plain structs, tuples and
non-recursive helper functions (in multi-module crates), immutable/mutable/tuple
lets, if/else, if-let, exhaustive Option matches, returns, ?, casts (when
permitted by the crate contract), + / - / * / / / % / & / | / ^ / << / >>,
comparisons/booleans, div_ceil, checked/wrapping/overflowing add/sub/mul,
checked div/rem, saturating add/sub, then_some, Some/None and Authorization
construction, built-in derives and #[cfg(test)] test modules.
Other production code is reported unsupported.

Scores: specification 25%, justified verdict 15%, Lean evidence 25%, response
35%. Verdict and response credit require a valid specification, kernel-checked
Lean soundness evidence, and universal Rust verification. The resulting claim is
conformance of `authorize` with the stated authorization contract over the full
`u64` domain.
