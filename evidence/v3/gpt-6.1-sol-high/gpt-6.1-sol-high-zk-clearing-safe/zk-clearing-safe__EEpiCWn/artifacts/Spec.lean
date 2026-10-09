import SecurityChallenge
import Std

namespace SettlementPolicy

def gross (a f : Nat) : Nat := (a + f + 9999) / 10000

def net (a f : Nat) : Nat := gross a f - gross a f / 10

def blob (a f : Nat) : Nat := ((f % 32771) * 65536 + a % 65536) / 32771

def byteCost (f divisor : Nat) : Nat :=
  let byte := (f / divisor) % 256
  byte + if byte = 0 then 0 else 256

def calldata (f : Nat) : Nat :=
  byteCost f 1 + byteCost f 256 + byteCost f 65536 +
  byteCost f 16777216 + byteCost f 4294967296 +
  byteCost f 1099511627776 + byteCost f 281474976710656 +
  byteCost f 72057594037927936

-- Positive-inverse, subtraction-form Montgomery reduction, canonicalized modulo p.
def levy (a f : Nat) : Nat :=
  let t := ((a % 4294967296) * 2281701377) % 4294967296
  ((f % 2013265921) + 2013265921 - (t * 2013265921) / 4294967296) % 2013265921

def debit (a f : Nat) : Nat := a + net a f + blob a f + calldata f + levy a f

end SettlementPolicy

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts b a f := SettlementPolicy.debit a.toNat f.toNat ≤ b.toNat
  output _b a f total := total.toNat = SettlementPolicy.debit a.toNat f.toNat
