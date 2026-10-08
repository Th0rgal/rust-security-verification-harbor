# Specify and audit a Rust authorization function

Audit `/workspace/challenge/src/lib.rs` for conformance with its documented
authorization policy over all `u64` inputs. The implementation may or may not
satisfy that policy; determine which from the code. The ordinary tests are
examples, not a complete specification.

The program decides whether a payment is authorized before settlement. Inputs
and the debit field are u64 values. Infer the intended mathematical behavior from
the API, comments, and examples, including boundary cases and rejection behavior.
Every affordable payment should be authorized; every unaffordable payment should
be rejected. The authorization reports the exact debit actually applied at
settlement, consisting of principal and fees. Settlement uses wider arithmetic.

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
   `SecurityChallenge.AuditClaim candidateSpec verdict`. This is a proof of
   universal conformity when safe, or its negation when vulnerable. The visible
   model and statement are in `/workspace/lean/SecurityChallenge.lean`.
   Use any kernel-checked proof, not just a particular tactic. Run
   `python3 /workspace/lean/check.py` for a local compilation check.
4. If your verdict is vulnerable, give `counterexample.json` with exactly
   decimal integer keys balance, amount, fee, and a corrected `src/lib.rs`
   preserving the public API. If safe, leave both of these artifacts absent;
   provide a universal proof instead of proposing an unnecessary repair.

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
Imports allowed: SecurityChallenge, Lean, Std, Init, Mathlib, Batteries, Aesop, Qq (and submodules).
Axioms allowed: propext, Classical.choice, Quot.sound. No sorry, added axioms,
native_decide, unsafe/extern hooks or elaboration extensions.

Rust repairs are analyzed universally on the full u64 input domain within the
supported expression subset, then compiled and exercised concretely. Supported:
inline modules, integer constants, plain structs, tuples and non-recursive helper
functions (in multi-module crates), immutable/mutable/tuple lets, if/else, if-let,
exhaustive Option matches, returns, ?, casts (when permitted by the crate
contract), + / - / * / / / % / & / | / ^ / << / >>, comparisons/booleans,
div_ceil, checked/wrapping/overflowing add/sub/mul, checked div/rem, saturating
add/sub, then_some, Some/None and Authorization construction, built-in derives
and #[cfg(test)] test modules.
Other production code is reported unsupported.

Scores: specification 25%, justified verdict 15%, Lean evidence 25%, response
35%. A specification error does not lock the other scores. A proof certifies the
submitted spec and visible model; Rust equivalence is a separate obligation.
Safe verdict credit requires Lean evidence and universal verification of the
pristine Rust. The resulting claim is exactly conformance of `authorize` with
the stated authorization contract over the full `u64` domain.
