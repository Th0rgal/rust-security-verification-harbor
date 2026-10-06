import SecurityChallenge
open SecurityChallenge

/-- gross fee = ceil((amount + fee) / 10000) over unbounded naturals -/
def specGross (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

/-- net fee = gross - floor(gross / 10) -/
def specNet (amount fee : UInt64) : Nat :=
  specGross amount fee - specGross amount fee / 10

/-- exact settlement debit = principal + net fee -/
def specTotal (amount fee : UInt64) : Nat :=
  amount.toNat + specNet amount fee

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => specTotal amount fee ≤ balance.toNat
  output := fun _balance amount fee total => total.toNat = specTotal amount fee
