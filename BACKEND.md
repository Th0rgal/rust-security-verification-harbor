# Verifier semantics and limits

## Reference policy and independent obligations

For inputs balance, amount, fee in [0, 2^64-1], let S be the unbounded
mathematical debit defined by the task family (`problem.txt`):
- In `authorization`, `S = amount + fee`.
- In `settlement`, `settlement-modular`, and `settlement-engine`,
  `gross_fee = ceil((amount + fee) / 10_000)`, `rebate = floor(gross_fee / 10)`,
  and `S = amount + (gross_fee - rebate)`.
- In `goldilocks` (Goldilocks prime `P = 2^64 - 2^32 + 1`),
  `S = floor(amount / 2^32) + ((amount + fee * 2^64) mod P)`.
- In `whirlpool` (fee rate denominator `1_000_000`),
  `S = floor(amount / 2) + ceil((amount + fee * 2^64) / 1_000_000)`.
- In `plonky3` (BabyBear prime `P = 2013265921`, `R^{-1} mod P = 943718400`),
  `S = amount + ((((amount mod 2^32) + (fee mod P) * 2^32) * 943718400) mod P)`.
- In `succinct` (`tov/succinct-rs` SWAR broadword byte detection, `b_i(fee) = floor(fee / 256^i) mod 256`),
  `S = floor(amount / 2) + sum_{i=0..7} b_i(fee) + 256 * |{i in 0..7 | b_i(fee) > 0}|`.
- In `openpql` (`solve-poker/Poker-Query-Language` 4-level mixed-radix indexing),
  `S = floor(amount / 2) + min(fee mod 65536, 32767)`.
- In `ruint` (`alloy-rs/ruint` Möller-Granlund 2-by-1 normalized division, `D = 32771`, `B = 65536`),
  `S = floor(amount / 2) + floor(((fee mod D) * B + (amount mod B)) / D)`.

The hidden business contract accepts iff S <= balance, and returns S on
acceptance. Because balance is a u64, S <= balance
also implies S fits u64; no separate overflow point is double-counted.

The four spec facets are:
1. accepts -> S <= balance.
2. S <= balance -> accepts.
3. On accepted inputs every allowed output equals S, and output is unique.
4. There is at least one accepted input, and every accepted input has a bounded
   u64 output satisfying candidate.output.

Facet 3 also requires facet 4's nonvacuity/existence sub-obligations before it
earns credit. Each raw query remains visible in details. Output constraints for
rejected inputs are irrelevant to an Option-valued API. An all-False spec earns
only safety (one quarter of the spec checkpoint).

## Lean-native specification pipeline

The agent writes complete Lean Spec.lean/Audit.lean files; helper definitions and
lemmas are supported, and precompiled `Mathlib`, `Batteries`, `Aesop`, `Qq`, `Std`,
and `Init` are available on `LEAN_PATH`. candidateSpec must have type AuthorizationSpec
and verdict type AuditVerdict. Proof.lean is a term for the fixed AuditClaim candidateSpec
verdict, wrapped in a trusted theorem declaration. No proof tactic is required.

Each stage elaborates in a fresh OS sandbox. Only bounded regular source files
and frozen predecessor .olean dependencies are copied in. All elaborator output
is removed, then only the target .olean and original frozen dependencies are
restored. leanchecker independently replays the serialized kernel declarations.
A trusted auditor loads modules with loadExts=false and checks types plus the
transitive dependency axioms (propext, Classical.choice, Quot.sound only), rejecting
unsafe dependencies. It unfolds the verdict to an enumerated constructor.

SpecAudit lowers elaborated Lean Exprs. It dispatches primitive heads, beta/let
reductions, structure projections and recursive definition unfolding, preserving
conditional heads. It never reads the user's expression as JSON. Accepted
operations: Nat constants, input UInt64.toNat, Nat.add, Nat.sub (truncated at zero),
Nat.mul (including general non-linear input products), Nat.div/Nat.mod by a positive
constant or strictly positive expression, Nat.le/Nat.lt, Nat/Prop equality, And, Or,
Not, Iff, nondependent implication and nondependent ite.
UInt64 arithmetic in specs, quantified binders, unsupported recursors and unknown
heads are unsupported.
Closed UInt64.toNat literals can reduce to constants. Expression bounds and
normalization fuel are finite; solver, process, memory and output limits apply.

The typed intermediate tree is converted to Z3 integer/Boolean expressions with
exact bounded domains. For large constant divisors (`>= 1_000_000`) or variable
divisors (e.g., `goldilocks`, `whirlpool`, `plonky3`), `div` and `mod` subterms
are purified into fresh Euclidean quotient/remainder variables (`N = q * D + r`,
`0 <= r < D`) so Z3 `QF_NIA` solves equivalence and existence queries without
timeout. The output-existence obligation quantifies over bounded
integer totalDebit (reducing directly when `candidate.output` has an isolated
`totalDebit = rhs` equality). A SAT query returns concrete failing inputs; UNSAT
establishes the obligation in the supported theory. Unknown/timeouts are unresolved
and do not receive success credit. Unsupported output expressions do not erase scores
for separately supported accepts facets. There is currently no general Lean
automation fallback for arbitrary specs.

Lean checks proofs over the visible original arithmetic model. Its safe claim is
universal accepted/not-accepted equivalence plus valid returned output; its
vulnerable claim is the negation of that conformity. These are statements about
the submitted spec. The spec checkpoint independently judges whether it captures
the hidden business contract. The Lean proof neither certifies the submitted Rust
patch nor kernel-proves the Rust/model correspondence. That trusted relationship
is explicitly part of the benchmark design.

## Rust backend

rust_symbolic.py uses typed integer/bit-vector path semantics and Z3 over all u64
inputs for a finite expression subset. Unsupported syntax is rejected before
compilation/execution. The original Rust is pristine inside the verifier. Compiled
optimized Rust probes compare boundaries, reproducible random cases and every SMT
counterexample; sampling never substitutes for the universal SMT result.

Supported production code consists of Authorization and authorize, module-level
integer constants, inline modules/structs/non-recursive helpers,
immutable lets/shadowing, tuple destructuring lets (`let (d, borrow) = ...`),
if/else, if-let, exhaustive Option matches,
returns, ?, casts (`u32`, `u64`, `u128` when permitted by the crate contract; `u128` is forbidden in
pure-u64 tasks), arithmetic/comparisons/booleans, bitwise/shift operators (`&`, `|`, `^`, `<<`, `>>`),
div_ceil, checked/wrapping/overflowing/borrowing add/sub/mul, checked div/rem/shl/shr,
saturating add/sub, then_some, Some/None and Authorization construction. Built-in derives and cfg(test) modules
are accepted. Loops, macros, unsafe and extra dependencies are outside the
accepted production subset. The soundness claim is scoped to this subset and to
the functional authorization properties above. Rust/model semantic alignment is
reviewed and regression-tested; it is not a Lean theorem.

## Isolation and score scope

Harbor copies only declared artifacts into a separate offline verifier image.
The verifier imports no agent-written trusted models/configuration. Untrusted Lean
compilation uses Landlock filesystem restrictions and seccomp network/process
effects restrictions; failure to establish isolation is infrastructure_error.
Serialized modules are imported as data, with no candidate extensions loaded.
Symlinks and oversized source artifacts are rejected. In the safe task,
counterexample/repair artifacts must be absent: metadata detects even binary,
oversized or symlink artifacts without reading them.

A correct vulnerable verdict receives its own score; witness and repair are
independently evaluated even if Spec.lean fails. A safe verdict earns score only
with valid Lean evidence and universal + concrete pristine Rust conformity, and
its response must omit unnecessary repair/witness artifacts. A successful safe
submission establishes conformance with the authorization contract for every
`u64` input.

## Versioning

v3 uses real Lean specs and two symmetric tasks with byte-identical instruction.md.
Only the supplied original program/model and the trusted variant/configuration
differ. v1/v2 JSON fixtures and results are historical; the old GLM score cannot
be transferred to this new interface. Both variants require a fresh model run.

The module subset requires globally unique production item names and rejects
renamed imports (`use ... as ...`), external imports, and qualified struct
constructors. Qualified function/constant paths must resolve exactly. Its short-name resolver cannot represent
Rust lexical collisions or import aliases, so these forms receive no credit.

GitHub CI builds a public Lean base from the pinned Ubuntu amd64 manifest and
the SHA-256-verified official Lean 4.31.0 release (`.github/lean-base.Dockerfile`),
then runs the same offline selftest as the benchmark verifier. This avoids
requiring access to the benchmark registry image on clean runners.
