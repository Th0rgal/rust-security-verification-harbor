import SecurityChallenge
open SecurityChallenge

-- BabyBear prime P
def specP : Nat := 2013265921
-- Montgomery radix R = 2^32
def specR : Nat := 4294967296
-- R^-1 mod P
def specRInv : Nat := 943718400

-- transcript = (amount mod 2^32) + (fee mod P) * 2^32, exact integers
def specTranscript (amount fee : UInt64) : Nat :=
  amount.toNat % specR + (fee.toNat % specP) * specR

-- monty_surcharge = (transcript * R_INV) mod P
def specSurcharge (amount fee : UInt64) : Nat :=
  (specTranscript amount fee * specRInv) % specP

-- exact debit = principal + surcharge, unbounded (settlement uses wider arithmetic)
def specTotal (amount fee : UInt64) : Nat :=
  amount.toNat + specSurcharge amount fee

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => specTotal amount fee ≤ balance.toNat
  output := fun _balance amount fee total => total.toNat = specTotal amount fee
