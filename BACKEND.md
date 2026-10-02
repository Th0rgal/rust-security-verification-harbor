# Verifier semantics and limits

## Reference policy and independent obligations

For inputs balance, amount, fee in [0, 2^64-1], let S be the unbounded
mathematical amount + fee. The hidden business contract accepts iff S <= balance,
and returns S on acceptance. Because balance is a u64, S <= balance also implies
S fits u64; no separate overflow point is double-counted.

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
lemmas are supported. candidateSpec must have type AuthorizationSpec and verdict
type AuditVerdict. Proof.lean is a term for the fixed AuditClaim candidateSpec
verdict, wrapped in a trusted theorem declaration. No proof tactic is required.

Each stage elaborates in a fresh OS sandbox. Only bounded regular source files
and frozen predecessor .olean dependencies are copied in. All elaborator output
is removed, then only the target .olean and original frozen dependencies are
restored. leanchecker independently replays the serialized kernel declarations.
A trusted auditor loads modules with loadExts=false and checks types plus the
transitive dependency axioms (propext, Classical.choice, Quot.sound only), rejecting
unsafe dependencies. It unfolds the verdict to an enumerated constructor.

SpecAudit lowers elaborated Lean Exprs. It dispatches primitive heads, beta/let
reductions, structure projections and one-layer definition unfolding, preserving
conditional heads. It never reads the user's expression as JSON. Accepted
operations: Nat constants, input UInt64.toNat, Nat.add, Nat.sub (truncated at zero),
Nat.le/Nat.lt, Nat/Prop equality, And, Or, Not, Iff, nondependent implication and
nondependent ite. UInt64 arithmetic in specs, quantified binders, unsupported
recursors, nonlinear input arithmetic and unknown heads are unsupported.
Closed UInt64.toNat literals can reduce to constants. Expression bounds and
normalization fuel are finite; solver, process, memory and output limits apply.

The typed intermediate tree is converted to Z3 integer/Boolean expressions with
exact bounded domains. The output-existence obligation quantifies over bounded
integer totalDebit. A SAT query returns concrete failing inputs; UNSAT establishes
the obligation in the supported theory. Unknown/timeouts are unresolved and do
not receive success credit. Unsupported output expressions do not erase scores
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

Supported production code consists of Authorization and authorize, immutable
lets/shadowing, if/else, if-let, exhaustive Option matches, returns, ?, casts,
arithmetic/comparisons/booleans, checked/wrapping add/sub, saturating_add, then_some,
Some/None and Authorization construction. Built-in derives and cfg(test) modules
are accepted. Loops, macros, helpers and extra dependencies are outside the
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
