import SecurityChallenge

-- Exact settlement arithmetic; neither the product nor the debit wraps.
def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat +
    (((amount.toNat % 4294967296 + (fee.toNat % 2013265921) * 4294967296)
       * 943718400) % 2013265921)

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output _ amount fee totalDebit := totalDebit.toNat = settlementDebit amount fee
