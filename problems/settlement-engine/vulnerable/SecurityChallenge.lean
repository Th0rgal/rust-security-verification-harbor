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
def makerRebateCapDivisor : UInt64 := 5
def treasuryCutDivisor : UInt64 := 4
def flashDenom : UInt64 := 5000
def flashMaxRem : UInt64 := 4999
def u64ModFlashQuot : UInt64 := 3689348814741910
def u64ModFlashRem : UInt64 := 1616
def institutionalBandMin : UInt64 := 10000000000000
def u64Max : UInt64 := 18446744073709551615

structure WordSum where
  lowWord : UInt64
  highCarry : Bool

def addU64WithCarry (lhs rhs : UInt64) : WordSum :=
  let lowWord := lhs + rhs
  { lowWord := lowWord, highCarry := decide (lowWord < lhs) }

def isInstitutionalNotional (sum : WordSum) : Bool :=
  if sum.highCarry then
    true
  else
    decide (institutionalBandMin ≤ sum.lowWord)

def floorDivBpsU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (sum.lowWord / bpsDenom) + (foldedRem / bpsDenom)
  else
    sum.lowWord / bpsDenom

def ceilDivBpsU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (sum.lowWord / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
  else
    let biased := sum.lowWord + bpsMaxRem
    if biased < sum.lowWord then
      (sum.lowWord / bpsDenom) + ((biased + u64ModBpsRem) / bpsDenom)
    else
      biased / bpsDenom

structure FeeSchedule where
  bpsDenom : UInt64
  rebateDivisor : UInt64
  makerCapDivisor : UInt64

structure FeeQuote where
  grossFee : UInt64
  rebate : UInt64
  netFee : UInt64

def defaultSchedule : FeeSchedule :=
  { bpsDenom := bpsDenom, rebateDivisor := rebateDivisor, makerCapDivisor := makerRebateCapDivisor }

def computeTierRebate (grossFee : UInt64) : UInt64 :=
  grossFee / rebateDivisor

def computeCappedMakerRebate (grossFee capBasis : UInt64) : UInt64 :=
  let baseRebate := grossFee / rebateDivisor
  let maxRebate := capBasis / makerRebateCapDivisor
  if baseRebate ≤ maxRebate then baseRebate else maxRebate

def evaluateSettlementFee (sum : WordSum) : FeeQuote :=
  let grossFee := ceilDivBpsU64 sum
  let rebate := computeTierRebate grossFee
  let netFee := grossFee - rebate
  { grossFee := grossFee, rebate := rebate, netFee := netFee }

def evaluatePassiveFloorFee (sum : WordSum) : FeeQuote :=
  let grossFee := floorDivBpsU64 sum
  let rebate := computeTierRebate grossFee
  let netFee := grossFee - rebate
  { grossFee := grossFee, rebate := rebate, netFee := netFee }

structure PoolReserveQuote where
  treasuryCut : UInt64
  lpRetention : UInt64

def splitPoolReserve (quote : FeeQuote) : PoolReserveQuote :=
  let treasuryCut := quote.netFee / treasuryCutDivisor
  let lpRetention := quote.netFee - treasuryCut
  { treasuryCut := treasuryCut, lpRetention := lpRetention }

def quoteLpRetention (quote : FeeQuote) : UInt64 :=
  (splitPoolReserve quote).lpRetention

structure FlashLoanReceipt where
  principal : UInt64
  flashLevy : UInt64
  totalRepayment : UInt64

def assessFlashFeeCeil (principal surcharge : UInt64) : UInt64 :=
  let sum := addU64WithCarry principal surcharge
  if sum.highCarry then
    let foldedRem := (sum.lowWord % flashDenom) + u64ModFlashRem
    u64ModFlashQuot + (sum.lowWord / flashDenom) + ((foldedRem + flashMaxRem) / flashDenom)
  else
    let biased := sum.lowWord + flashMaxRem
    if biased < sum.lowWord then
      (sum.lowWord / flashDenom) + (((sum.lowWord % flashDenom) + flashMaxRem) / flashDenom)
    else
      biased / flashDenom

def quoteFlashRepayment (principal surcharge : UInt64) : Option FlashLoanReceipt :=
  let flashLevy := assessFlashFeeCeil principal surcharge
  if flashLevy ≤ u64Max - principal then
    some { principal := principal, flashLevy := flashLevy, totalRepayment := principal + flashLevy }
  else
    none

structure SettlementTicket where
  principal : UInt64
  grossFee : UInt64
  rebate : UInt64
  netFee : UInt64
  totalDebit : UInt64

def assembleTicket (amount : UInt64) (feeQuote : FeeQuote) : Option SettlementTicket :=
  if feeQuote.netFee ≤ u64Max - amount then
    some {
      principal := amount
      grossFee := feeQuote.grossFee
      rebate := feeQuote.rebate
      netFee := feeQuote.netFee
      totalDebit := amount + feeQuote.netFee
    }
  else
    none

def quoteSettlementTicket (amount fee : UInt64) : Option SettlementTicket :=
  let notionalSum := addU64WithCarry amount fee
  let feeQuote := evaluateSettlementFee notionalSum
  assembleTicket amount feeQuote

def commitTicket (balance : UInt64) (ticket : SettlementTicket) : Option UInt64 :=
  if ticket.totalDebit ≤ balance then
    some ticket.totalDebit
  else
    none

-- Visible program model, not the hidden policy used to grade specifications.
def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  match quoteSettlementTicket amount fee with
  | some ticket => commitTicket balance ticket
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
