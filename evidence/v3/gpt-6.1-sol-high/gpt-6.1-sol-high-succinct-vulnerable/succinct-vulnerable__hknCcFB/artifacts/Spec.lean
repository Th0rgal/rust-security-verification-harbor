import SecurityChallenge

namespace PaymentPolicy

-- Extract each byte as an exact natural number, independently of SWAR.
def feeByte (fee : UInt64) (i : Nat) : Nat :=
  (fee.toNat / (256 ^ i)) % 256

def active (b : Nat) : Nat := if b = 0 then 0 else 1

def activeBytes (fee : UInt64) : Nat :=
  active (feeByte fee 0) + active (feeByte fee 1) +
  active (feeByte fee 2) + active (feeByte fee 3) +
  active (feeByte fee 4) + active (feeByte fee 5) +
  active (feeByte fee 6) + active (feeByte fee 7)

def byteSum (fee : UInt64) : Nat :=
  feeByte fee 0 + feeByte fee 1 + feeByte fee 2 + feeByte fee 3 +
  feeByte fee 4 + feeByte fee 5 + feeByte fee 6 + feeByte fee 7

-- Settlement arithmetic is exact, not arithmetic modulo 2^64.
def debit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + 256 * activeBytes fee + byteSum fee

end PaymentPolicy

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee =>
    PaymentPolicy.debit amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit =>
    totalDebit.toNat = PaymentPolicy.debit amount fee
