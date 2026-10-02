import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

-- Visible program models, not the hidden policy used to grade specifications.
def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  let total := amount + fee
  if total.toNat ≤ balance.toNat then some total else none

def Conforms (spec : AuthorizationSpec)
    (authorize : UInt64 → UInt64 → UInt64 → Option UInt64) : Prop :=
  (∀ b a f, (∃ total, authorize b a f = some total) ↔ spec.accepts b a f) ∧
  (∀ b a f total, authorize b a f = some total → spec.output b a f total)

def AuditClaim (spec : AuthorizationSpec) (verdict : AuditVerdict) : Prop :=
  match verdict with
  | .safe => Conforms spec challengeAuthorize
  | .vulnerable => ¬ Conforms spec challengeAuthorize

end SecurityChallenge
