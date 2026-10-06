import SecurityChallenge
open SecurityChallenge

/-- Gross protocol fee: ceil((amount + fee) / 10000) over exact naturals. -/
def specGrossFee (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

/-- Tier rebate: floor(gross / 10). -/
def specRebate (amount fee : UInt64) : Nat :=
  specGrossFee amount fee / 10

/-- Exact net settlement debit: amount + (gross - rebate), unbounded. -/
def specTotalDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (specGrossFee amount fee - specRebate amount fee)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => specTotalDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total => total.toNat = specTotalDebit amount fee
