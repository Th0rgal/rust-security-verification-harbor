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
def highValueThreshold : UInt64 := 1000000000000

structure SumFold where
  lowWord : UInt64
  wrappedU64 : Bool

def foldU64Sum (amount fee : UInt64) : SumFold :=
  let lowWord := amount + fee
  { lowWord := lowWord, wrappedU64 := decide (lowWord < amount) }

def floorDivBpsFolded (fold : SumFold) : UInt64 :=
  if fold.wrappedU64 then
    let remSum := (fold.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (fold.lowWord / bpsDenom) + (remSum / bpsDenom)
  else
    fold.lowWord / bpsDenom

def ceilDivBpsFolded (fold : SumFold) : UInt64 :=
  if fold.wrappedU64 then
    let foldedRem := (fold.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (fold.lowWord / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
  else
    let biased := fold.lowWord + bpsMaxRem
    if biased < fold.lowWord then
      (fold.lowWord / bpsDenom) + ((biased + u64ModBpsRem) / bpsDenom)
    else
      biased / bpsDenom

structure FeeBreakdown where
  grossFee : UInt64
  rebate : UInt64
  netFee : UInt64

def tierRebateFloor (grossFee : UInt64) : UInt64 :=
  grossFee / rebateDivisor

def computeFeeBreakdown (grossFee : UInt64) : FeeBreakdown :=
  let rebate := tierRebateFloor grossFee
  let netFee := grossFee - rebate
  { grossFee := grossFee, rebate := rebate, netFee := netFee }

def isHighVolumeLevy (breakdown : FeeBreakdown) : Bool :=
  decide (highValueThreshold ≤ breakdown.grossFee)

structure SettlementQuote where
  principal : UInt64
  netFee : UInt64
  totalDebit : UInt64

def buildSettlementQuote (amount : UInt64) (breakdown : FeeBreakdown) : Option SettlementQuote :=
  if breakdown.netFee ≤ u64Max - amount then
    some { principal := amount, netFee := breakdown.netFee, totalDebit := amount + breakdown.netFee }
  else
    none

def verifyAffordability (balance : UInt64) (quote : SettlementQuote) : Option UInt64 :=
  if quote.totalDebit ≤ balance then
    some quote.totalDebit
  else
    none

-- Visible program model, not the hidden policy used to grade specifications.
def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  let fold := foldU64Sum amount fee
  let grossFee := ceilDivBpsFolded fold
  let breakdown := computeFeeBreakdown grossFee
  match buildSettlementQuote amount breakdown with
  | some quote => verifyAffordability balance quote
  | none => none

def Conforms (spec : AuthorizationSpec)
    (authorize : UInt64 → UInt64 → UInt64 → Option UInt64) : Prop :=
  (∀ b a f, (∃ total, authorize b a f = some total) ↔ spec.accepts b a f) ∧
  (∀ b a f total, authorize b a f = some total → spec.output b a f total)

def AuditClaim (spec : AuthorizationSpec) (verdict : AuditVerdict) : Prop :=
  match verdict with
  | .safe => Conforms spec challengeAuthorize
  | .vulnerable => ¬ Conforms spec challengeAuthorize

end SecurityChallenge
