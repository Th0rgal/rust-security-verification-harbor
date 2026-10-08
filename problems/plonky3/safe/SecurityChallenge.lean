import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def babyBearP : UInt64 := 2013265921
def babyBearMu : UInt64 := 2281701377
def limbBase : UInt64 := 4294967296
def limbMask : UInt64 := 4294967295
def u64Max : UInt64 := 18446744073709551615

structure PlonkyQuote where
  principal : UInt64
  montySurcharge : UInt64
  totalDebit : UInt64

def packTranscript (amount fee : UInt64) : UInt64 :=
  let low := amount % limbBase
  let high := fee % babyBearP
  limbBase * high + low

def montyQuotient (x : UInt64) : UInt64 :=
  let xLo := x % limbBase
  (babyBearMu * xLo) % limbBase

def montyReduce (x : UInt64) : UInt64 :=
  let t := montyQuotient x
  let u := babyBearP * t
  let diff := x - u
  let hi := diff / limbBase
  if x < u then
    babyBearP + hi - limbBase
  else
    hi

def buildQuote (amount fee : UInt64) : Option PlonkyQuote :=
  let transcript := packTranscript amount fee
  let montySurcharge := montyReduce transcript
  if montySurcharge ≤ u64Max - amount then
    some {
      principal := amount,
      montySurcharge := montySurcharge,
      totalDebit := amount + montySurcharge
    }
  else
    none

def verifyAffordability (balance : UInt64) (quote : PlonkyQuote) : Option UInt64 :=
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
