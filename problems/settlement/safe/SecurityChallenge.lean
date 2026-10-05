import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def bpsDenom : UInt64 := 10000
def bpsMaxRem : UInt64 := 9999
def u64ModBpsQuot : UInt64 := 1844674407370955
def u64ModBpsRem : UInt64 := 1616
def rebateDivisor : UInt64 := 10
def u64Max : UInt64 := 18446744073709551615

-- Visible program model, not the hidden policy used to grade specifications.
def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  let rawSum := amount + fee
  let grossFee :=
    if rawSum < amount then
      let foldedRem := (rawSum % bpsDenom) + u64ModBpsRem
      u64ModBpsQuot + (rawSum / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
    else
      let biased := rawSum + bpsMaxRem
      if biased < rawSum then
        (rawSum / bpsDenom) + (((rawSum % bpsDenom) + bpsMaxRem) / bpsDenom)
      else
        biased / bpsDenom
  let rebate := grossFee / rebateDivisor
  let netFee := grossFee - rebate
  if netFee ≤ u64Max - amount then
    let total := amount + netFee
    if total ≤ balance then
      some total
    else
      none
  else
    none

def Conforms (spec : AuthorizationSpec)
    (authorize : UInt64 → UInt64 → UInt64 → Option UInt64) : Prop :=
  (∀ b a f, (∃ total, authorize b a f = some total) ↔ spec.accepts b a f) ∧
  (∀ b a f total, authorize b a f = some total → spec.output b a f total)

def AuditClaim (spec : AuthorizationSpec) (verdict : AuditVerdict) : Prop :=
  match verdict with
  | .safe => Conforms spec challengeAuthorize
  | .vulnerable => ¬ Conforms spec challengeAuthorize

end SecurityChallenge
