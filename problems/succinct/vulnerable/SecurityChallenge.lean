namespace SecurityChallenge

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def l8Mask : UInt64 := 0x0101010101010101
def h8Mask : UInt64 := 0x8080808080808080
def m16Mask : UInt64 := 0x00FF00FF00FF00FF
def l16Mask : UInt64 := 0x0001000100010001

structure SuccinctQuote where
  principalShare : UInt64
  activeBytes : UInt64
  byteSum : UInt64
  totalDebit : UInt64

def uNz8 (x : UInt64) : UInt64 :=
  ((x ||| h8Mask) - l8Mask) &&& h8Mask

def countNzBytes (x : UInt64) : UInt64 :=
  (((uNz8 x) >>> 7) * l8Mask) >>> 56

def sumBytes (x : UInt64) : UInt64 :=
  let pairs := (x &&& m16Mask) + ((x >>> 8) &&& m16Mask)
  ((pairs * l16Mask) >>> 48) &&& 0xFFFF

def buildQuote (amount fee : UInt64) : Option SuccinctQuote :=
  let principalShare := amount >>> 1
  let activeBytes := countNzBytes fee
  let byteSum := sumBytes fee
  let totalDebit := principalShare + (activeBytes <<< 8) + byteSum
  some {
    principalShare := principalShare,
    activeBytes := activeBytes,
    byteSum := byteSum,
    totalDebit := totalDebit
  }

def verifyAffordability (balance : UInt64) (quote : SuccinctQuote) : Option UInt64 :=
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
