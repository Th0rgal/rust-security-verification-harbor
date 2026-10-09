import Lean
import LeanModel.Constants

namespace LeanModel.GoldilocksField

open LeanModel.Constants

structure GoldilocksQuote where
  foldedLow : UInt64
  canonicalResidue : UInt64
  bridgeFee : UInt64

def reduceGoldilocksStep1 (xLo xHi : UInt64) : UInt64 × Bool :=
  let xHiHi : UInt64 := xHi >>> 32
  (xLo - xHiHi, decide (xLo < xHiHi))

def reduceGoldilocks128 (xLo xHi : UInt64) : UInt64 :=
  let xHiLo : UInt64 := xHi &&& goldilocksEps
  let (t0, borrow) := reduceGoldilocksStep1 xLo xHi
  let t1 : UInt64 := if borrow then t0 - goldilocksEps else t0
  let prod : UInt64 := xHiLo * goldilocksEps
  let t2 : UInt64 := t1 + prod
  let carry : Bool := decide (t2 < t1)
  let t3 : UInt64 := if carry then t2 + goldilocksEps else t2
  if goldilocksP ≤ t3 then
    t3 - goldilocksP
  else
    t3

def canonicalizeGoldilocksU64 (x : UInt64) : UInt64 :=
  if goldilocksP ≤ x then x - goldilocksP else x

def addGoldilocksMod (a b : UInt64) : UInt64 :=
  let s : UInt64 := a + b
  reduceGoldilocks128 s (if s < a then 1 else 0)

def subGoldilocksMod (a b : UInt64) : UInt64 :=
  let ca : UInt64 := canonicalizeGoldilocksU64 a
  let cb : UInt64 := canonicalizeGoldilocksU64 b
  if cb ≤ ca then ca - cb else (goldilocksP - cb) + ca

def foldGoldilocksChallenge (commitment challengeU32 : UInt64) : UInt64 :=
  let scalar : UInt64 := challengeU32 &&& low32Mask
  let loLimb : UInt64 := commitment &&& low32Mask
  let hiLimb : UInt64 := commitment >>> 32
  let prodLo : UInt64 := loLimb * scalar
  let prodHi : UInt64 := hiLimb * scalar
  let xLo : UInt64 := prodLo + (prodHi <<< 32)
  let carry : UInt64 := if xLo < prodLo then 1 else 0
  let xHi : UInt64 := (prodHi >>> 32) + carry
  reduceGoldilocks128 xLo xHi

def quoteBridgeVerifierFee (amount fee : UInt64) : GoldilocksQuote :=
  let (foldedLow, _) := reduceGoldilocksStep1 amount fee
  let canonicalResidue : UInt64 := reduceGoldilocks128 amount fee
  let bridgeFee : UInt64 := (amount >>> 32) + (canonicalResidue &&& low32Mask)
  {
    foldedLow := foldedLow
    canonicalResidue := canonicalResidue
    bridgeFee := bridgeFee
  }

end LeanModel.GoldilocksField
