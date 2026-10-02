import SecurityChallenge
open SecurityChallenge

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    amount.toNat + fee.toNat ≤ balance.toNat
  output := fun _ amount fee totalDebit =>
    totalDebit.toNat = amount.toNat + fee.toNat
