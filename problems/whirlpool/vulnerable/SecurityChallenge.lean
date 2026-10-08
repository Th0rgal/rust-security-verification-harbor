import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def limbBase : UInt64 := 4294967296
def feeRateMulValue : UInt64 := 1000000
def principalDivisor : UInt64 := 2
def u64Max : UInt64 := 18446744073709551615

structure U128Words where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64

structure DivStep where
  quot : UInt64
  rem : UInt64

structure DivResult where
  q0 : UInt64
  q1 : UInt64
  q2 : UInt64
  q3 : UInt64
  rem : UInt64

def splitU128 (amount fee : UInt64) : U128Words :=
  { w0 := amount % limbBase, w1 := amount / limbBase, w2 := fee % limbBase, w3 := fee / limbBase }

def divStep (rem word : UInt64) : DivStep :=
  let num := limbBase * rem + word
  { quot := num / feeRateMulValue, rem := num % feeRateMulValue }

def divWordChain (words : U128Words) : DivResult :=
  let step3 := divStep 0 words.w3
  let step2 := divStep step3.rem words.w2
  let step1 := divStep step2.rem words.w1
  let step0 := divStep step1.rem words.w0
  { q0 := step0.quot, q1 := step1.quot, q2 := step2.quot, q3 := step3.quot, rem := step0.rem }

def roundUpQuotient (div : DivResult) : U128Words :=
  let inc : UInt64 := if 0 < div.rem then 1 else 0
  let s0 := inc + div.q0
  let r0 := s0 % limbBase
  let c0 := s0 / limbBase
  let s1 := c0 + div.q1
  let r1 := s1 % limbBase
  let s2 := div.q2
  let r2 := s2 % limbBase
  let c2 := s2 / limbBase
  let r3 := c2 + div.q3
  { w0 := r0, w1 := r1, w2 := r2, w3 := r3 }

def tryIntoU64 (words : U128Words) : Option UInt64 :=
  if words.w2 = 0 ∧ words.w3 = 0 then
    some (limbBase * words.w1 + words.w0)
  else
    none

def divRoundUpFee (amount fee : UInt64) : Option UInt64 :=
  let words := splitU128 amount fee
  let div := divWordChain words
  let rounded := roundUpQuotient div
  tryIntoU64 rounded

structure WhirlpoolQuote where
  principalShare : UInt64
  grossFee : UInt64
  totalDebit : UInt64

def buildQuote (amount fee : UInt64) : Option WhirlpoolQuote :=
  let principalShare := amount / principalDivisor
  match divRoundUpFee amount fee with
  | some grossFee =>
    if grossFee ≤ u64Max - principalShare then
      some {
        principalShare := principalShare,
        grossFee := grossFee,
        totalDebit := principalShare + grossFee
      }
    else
      none
  | none => none

def verifyAffordability (balance : UInt64) (quote : WhirlpoolQuote) : Option UInt64 :=
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
