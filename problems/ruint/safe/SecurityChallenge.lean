namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def mg10Divisor : UInt64 := 0x8003
def mg10Reciprocal : UInt64 := 0xFFF4
def limbMask : UInt64 := 0xFFFF
def subBias : UInt64 := 0xC0000000

structure RuintQuote where
  u1 : UInt64
  u0 : UInt64
  quotient : UInt64
  totalDebit : UInt64

def div2x1Mg10 (u1 u0 : UInt64) : UInt64 :=
  let qFull : UInt64 := (u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)
  let q1 := qFull >>> 16
  let q0 := qFull &&& limbMask
  let r := (subBias + u0 - q1 * mg10Divisor) &&& limbMask
  let (qCorr, rCorr) :=
    if q0 < r then
      (q1 - 1, (r + mg10Divisor) &&& limbMask)
    else
      (q1, r)
  if mg10Divisor ≤ rCorr then
    qCorr + 1
  else
    qCorr

def buildQuote (amount fee : UInt64) : Option RuintQuote :=
  let u1 := fee % mg10Divisor
  let u0 := amount &&& limbMask
  let quotient := div2x1Mg10 u1 u0
  let totalDebit := (amount >>> 1) + quotient
  some {
    u1 := u1,
    u0 := u0,
    quotient := quotient,
    totalDebit := totalDebit
  }

def verifyAffordability (balance : UInt64) (quote : RuintQuote) : Option UInt64 :=
  if quote.totalDebit ≤ balance then
    some quote.totalDebit
  else
    none

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
