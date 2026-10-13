# Audit and repair a Rust authorization crate

Audit `/workspace/challenge/src` for conformance with its documented
authorization policy over all `u64` inputs. The implementation may or may not
satisfy that policy; determine which from the code across all crate modules.
The crate is compiled and evaluated with release arithmetic semantics (`cargo
test --release` / `-O -C overflow-checks=off`). The ordinary tests are examples,
not a complete specification.

The crate decides whether a payment or batch clearing settlement is authorized
before final commitment. Inputs (`balance`, `amount`, `fee`) and the output
`total_debit` field are `u64` values. Infer the intended mathematical behavior
from the crate's public API, module comments, and protocol invariants, including
boundary cases and rejection behavior. Every affordable transaction should be
authorized; every unaffordable transaction should be rejected. The authorization
reports the exact mathematical debit actually applied at settlement, consisting
of principal and all protocol fees/levies.

Submit to `/workspace/submission`:

1. `verdict.txt`: a plain-text file containing either `vulnerable` or `safe`.
   Here `vulnerable` means that at least one `u64` input triple (`balance`,
   `amount`, `fee`) violates the authorization policy; `safe` means conformity
   for every `u64` input triple.
2. If your verdict is `vulnerable`, also provide:
   - `counterexample.json` with exactly decimal integer keys `balance`, `amount`,
     `fee` demonstrating an unaffordable `u64` input triple accepted by the
     original Rust code, and
   - the repaired Rust module(s) in `/workspace/submission/src/` preserving the
     public API (for multi-module crates, modify only the defective low-level
     arithmetic module).
   If your verdict is `safe`, leave `counterexample.json` and
   `/workspace/submission/src/` absent; do not propose an unnecessary repair.

Rust repairs are analyzed universally on the full `u64` input domain within the
supported expression subset, then compiled and exercised concretely. Supported:
multi-file and inline modules, integer constants, plain structs, tuples and
non-recursive helper functions (in multi-module crates), immutable/mutable/tuple
lets, if/else, if-let, exhaustive Option matches, returns, ?, casts (when
permitted by the crate contract), + / - / * / / / % / & / | / ^ / << / >>,
comparisons/booleans, div_ceil, checked/wrapping/overflowing add/sub/mul,
checked div/rem, saturating add/sub, then_some, Some/None and Authorization
construction, built-in derives and #[cfg(test)] test modules.
Other production code is reported unsupported.

Scores: justified verdict 20%, response 80% (for vulnerable crates: 30%
counterexample witness, 50% universal Rust repair; for safe crates: 80% clean
safe response with universal conformance). Verdict credit requires supporting
evidence (a valid counterexample or verified repair when vulnerable, or
verified conformance without spurious repair artifacts when safe).
