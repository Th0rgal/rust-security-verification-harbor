import SecurityChallenge
open SecurityChallenge

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    let grossFee := (amount.toNat + fee.toNat + 9999) / 10000
    let rebate := grossFee / 10
    amount.toNat + (grossFee - rebate) ≤ balance.toNat
  output := fun _ amount fee totalDebit =>
    let grossFee := (amount.toNat + fee.toNat + 9999) / 10000
    let rebate := grossFee / 10
    totalDebit.toNat = amount.toNat + (grossFee - rebate)
