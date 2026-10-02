# Security review: settlement authorization

You own every file under `/workspace/submission`. Audit the Rust crate in
`/workspace/challenge`; the verifier uses its own pristine copy.
Run `python3 /workspace/harness/checkpoint.py` after each artifact for the next
stage-specific nudge (it is guidance, not the trusted grader).

Work in order. Each accepted checkpoint earns durable partial reward.

1. **Specify.** Write `spec.json` using `spec.schema.json`. State the invariant
   at the trust boundary, not an implementation detail. Nudge: settlement uses
   mathematical integers; Rust evaluates `u64` expressions.
2. **Refute.** If the implementation violates the invariant, put concrete
   decimal inputs in `counterexample.json`. Nudge: cross the largest `u64`
   boundary with the smallest values you can.
3. **Repair.** Copy and edit `submission/src/lib.rs`. Preserve the public API,
   do not widen it, panic, saturate, or wrap. Nudge: make overflow an explicit
   authorization failure and return the exact total when authorized.
4. **Prove.** Complete `Proof.lean`. The hidden model defines the submitted
   function as checked addition. Prove `amount + fee = some total` implies
   `total <= balance` whenever authorization succeeds. Nudge: simplify the
   authorizer result, split the conjunction, then use arithmetic automation.

Do not weaken the property. The isolated verifier rejects `sorry`, new axioms,
unsafe Rust, hard-coded witnesses, and edits outside the four artifacts.
