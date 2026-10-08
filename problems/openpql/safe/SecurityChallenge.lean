import Lean

namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def radixBase : UInt64 := 65536
def shift16 : UInt64 := 65536
def shift32 : UInt64 := 4294967296
def shift48 : UInt64 := 281474976710656
def halfDivisor : UInt64 := 2

structure OpenPqlQuote where
  principalShare : UInt64
  encodedIdx : UInt64
  indexSurcharge : UInt64
  totalDebit : UInt64

def clampDigit (a b : UInt64) : UInt64 :=
  if a < b then a else b - 1

def encodeMixedRadix (amount fee : UInt64) : UInt64 :=
  let b0 := (fee % radixBase) + 1
  let b1 := ((fee / shift16) % radixBase) + 1
  let b2 := ((fee / shift32) % radixBase) + 1
  let b3 := ((fee / shift48) % radixBase) + 1
  let a0 := amount % radixBase
  let a1 := (amount / shift16) % radixBase
  let a2 := (amount / shift32) % radixBase
  let a3 := (amount / shift48) % radixBase
  let d0 := clampDigit a0 b0
  let d1 := clampDigit a1 b1
  let d2 := clampDigit a2 b2
  let d3 := clampDigit a3 b3
  let o2 := b3
  let o1 := b2 * o2
  let o0 := b1 * o1
  d0 * o0 + d1 * o1 + d2 * o2 + d3

def buildQuote (amount fee : UInt64) : Option OpenPqlQuote :=
  let principalShare := amount / halfDivisor
  let encodedIdx := encodeMixedRadix amount fee
  let indexSurcharge := encodedIdx / halfDivisor
  let totalDebit := principalShare + indexSurcharge
  some {
    principalShare := principalShare,
    encodedIdx := encodedIdx,
    indexSurcharge := indexSurcharge,
    totalDebit := totalDebit
  }

def verifyAffordability (balance : UInt64) (quote : OpenPqlQuote) : Option UInt64 :=
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
