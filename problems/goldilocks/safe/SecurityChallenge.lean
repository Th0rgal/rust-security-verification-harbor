import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def goldilocksModulus : UInt64 := 18446744069414584321
def goldilocksEpsilon : UInt64 := 4294967295
def limbBase : UInt64 := 4294967296
def principalDivisor : UInt64 := 2
def u64Max : UInt64 := 18446744073709551615

structure TranscriptLimbs where
  low : UInt64
  mid : UInt64
  high : UInt64

def splitTranscript (amount fee : UInt64) : TranscriptLimbs :=
  { low := amount, mid := fee % limbBase, high := fee / limbBase }

def foldHighLimb (low high : UInt64) : UInt64 :=
  let low2 := low - high
  if low < high then
    goldilocksModulus + low2
  else
    low2

def foldMidLimb (low2 mid : UInt64) : UInt64 :=
  let product := goldilocksEpsilon * mid
  let sum1 := low2 + product
  if sum1 < low2 then
    goldilocksEpsilon + sum1
  else
    sum1

def canonicalize (folded : UInt64) : UInt64 :=
  if goldilocksModulus ≤ folded then
    folded - goldilocksModulus
  else
    folded

def reduce128 (amount fee : UInt64) : UInt64 :=
  let limbs := splitTranscript amount fee
  let low2 := foldHighLimb limbs.low limbs.high
  let folded := foldMidLimb low2 limbs.mid
  canonicalize folded

structure GoldilocksQuote where
  principalShare : UInt64
  fieldSurcharge : UInt64
  totalDebit : UInt64

def buildQuote (amount fee : UInt64) : Option GoldilocksQuote :=
  let principalShare := amount / principalDivisor
  let fieldSurcharge := reduce128 amount fee
  if fieldSurcharge ≤ u64Max - principalShare then
    some {
      principalShare := principalShare,
      fieldSurcharge := fieldSurcharge,
      totalDebit := principalShare + fieldSurcharge
    }
  else
    none

def verifyAffordability (balance : UInt64) (quote : GoldilocksQuote) : Option UInt64 :=
  if quote.totalDebit ≤ balance then
    some quote.totalDebit
  else
    none

-- Visible program model, not the hidden policy used to grade specifications.
def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  match buildQuote amount fee with
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
