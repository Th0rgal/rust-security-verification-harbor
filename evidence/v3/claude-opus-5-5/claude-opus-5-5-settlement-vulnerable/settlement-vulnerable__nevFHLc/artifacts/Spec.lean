import SecurityChallenge
open SecurityChallenge

/-- Exact unbounded policy debit: amount + (ceil((amount+fee)/10000) - floor(ceil(..)/10)). -/
def policyGross (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

def policyTotal (amount fee : UInt64) : Nat :=
  amount.toNat + (policyGross amount fee - policyGross amount fee / 10)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => policyTotal amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit => totalDebit.toNat = policyTotal amount fee
