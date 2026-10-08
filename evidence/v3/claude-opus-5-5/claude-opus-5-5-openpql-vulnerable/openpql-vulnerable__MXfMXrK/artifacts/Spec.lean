import SecurityChallenge
open SecurityChallenge

-- radix b_i = ((fee >> 16i) & 0xFFFF) + 1, in exact Nat arithmetic
def radixAt (fee : UInt64) (sh : Nat) : Nat := (fee.toNat / sh) % 65536 + 1
-- coordinate a_i = (amount >> 16i) & 0xFFFF
def coordAt (amount : UInt64) (sh : Nat) : Nat := (amount.toNat / sh) % 65536
-- d_i = min(a_i, b_i - 1)
def digitAt (amount fee : UInt64) (sh : Nat) : Nat :=
  if coordAt amount sh < radixAt fee sh then coordAt amount sh else radixAt fee sh - 1

-- exact mixed-radix index d0*o0 + d1*o1 + d2*o2 + d3 (no wraparound)
def policyIdx (amount fee : UInt64) : Nat :=
  digitAt amount fee 1 * (radixAt fee 65536 * (radixAt fee 4294967296 * radixAt fee 281474976710656))
  + digitAt amount fee 65536 * (radixAt fee 4294967296 * radixAt fee 281474976710656)
  + digitAt amount fee 4294967296 * radixAt fee 281474976710656
  + digitAt amount fee 281474976710656

-- exact debit floor(amount/2) + floor(idx/2)
def policyTotal (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + policyIdx amount fee / 2

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => policyTotal amount fee ≤ balance.toNat
  output := fun _balance amount fee total => total.toNat = policyTotal amount fee
