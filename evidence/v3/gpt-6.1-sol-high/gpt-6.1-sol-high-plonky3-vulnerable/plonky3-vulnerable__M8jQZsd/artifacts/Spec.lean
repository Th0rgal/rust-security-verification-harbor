import SecurityChallenge
open SecurityChallenge

-- The settlement debit, computed in unbounded integer arithmetic.
def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat +
    (((amount.toNat % 4294967296 +
       (fee.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921)

-- Authorization is exact affordability; output is the exact settlement debit.
def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => policyDebit amount fee ≤ balance.toNat
  output := fun balance amount fee totalDebit =>
    policyDebit amount fee ≤ balance.toNat ∧ totalDebit.toNat = policyDebit amount fee
