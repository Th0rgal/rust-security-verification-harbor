import SecurityChallenge

open SecurityChallenge

def isNz (b : Nat) : Nat := if 0 < b then 1 else 0

def byteAt (x i : Nat) : Nat := (x >>> (8 * i)) % 256

def zkClearingDebit (amount fee : UInt64) : Nat :=
  let a := amount.toNat
  let f := fee.toNat
  let grossBps := (a + f + 9999) / 10000
  let netBpsFee := grossBps - (grossBps / 10)
  let blobSlotQuotient := ((f % 32771) * 65536 + (a % 65536)) / 32771
  let b0 := f % 256
  let b1 := (f / 256) % 256
  let b2 := (f / 65536) % 256
  let b3 := (f / 16777216) % 256
  let b4 := (f / 4294967296) % 256
  let b5 := (f / 1099511627776) % 256
  let b6 := (f / 281474976710656) % 256
  let b7 := (f / 72057594037927936) % 256
  let active := isNz b0 + isNz b1 + isNz b2 + isNz b3 + isNz b4 + isNz b5 + isNz b6 + isNz b7
  let bsum := b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7
  let calldataSurcharge := active * 256 + bsum
  let proverLevy := (((a % 4294967296) + (f % 2013265921) * 4294967296) * 943718400) % 2013265921
  a + netBpsFee + blobSlotQuotient + calldataSurcharge + proverLevy

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    zkClearingDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = zkClearingDebit amount fee
