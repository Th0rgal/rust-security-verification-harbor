import Lean
import LeanModel.Constants

namespace LeanModel.WordMath

open LeanModel.Constants

structure WordSum where
  lowWord : UInt64
  highCarry : Bool

structure WordDiff where
  diffWord : UInt64
  underflowBorrow : Bool

def addU64WithCarry (lhs rhs : UInt64) : WordSum :=
  let lowWord := lhs + rhs
  { lowWord := lowWord, highCarry := decide (lowWord < lhs) }

def subU64WithBorrow (lhs rhs : UInt64) : WordDiff :=
  let diffWord := lhs - rhs
  { diffWord := diffWord, underflowBorrow := decide (lhs < rhs) }

def extractLowU16 (word : UInt64) : UInt64 :=
  word &&& limbMask

def extractLowU32 (word : UInt64) : UInt64 :=
  word &&& low32Mask

def extractHighU32 (word : UInt64) : UInt64 :=
  word >>> 32

def packU32Limbs (lowU32 highU32 : UInt64) : UInt64 :=
  (lowU32 &&& low32Mask) ||| ((highU32 &&& low32Mask) <<< 32)

def isInstitutionalNotional (sum : WordSum) : Bool :=
  if sum.highCarry then
    true
  else
    decide (institutionalBandMin ≤ sum.lowWord)

def remBpsU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    ((sum.lowWord % bpsDenom) + u64ModBpsRem) % bpsDenom
  else
    sum.lowWord % bpsDenom

def floorDivBpsU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (sum.lowWord / bpsDenom) + (foldedRem / bpsDenom)
  else
    sum.lowWord / bpsDenom

def ceilDivBpsU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (sum.lowWord / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
  else
    let biased := sum.lowWord + bpsMaxRem
    if biased < sum.lowWord then
      (sum.lowWord / bpsDenom) + ((biased + u64ModBpsRem) / bpsDenom)
    else
      biased / bpsDenom

def floorDivFlashU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % flashDenom) + u64ModFlashRem
    u64ModFlashQuot + (sum.lowWord / flashDenom) + (foldedRem / flashDenom)
  else
    sum.lowWord / flashDenom

def ceilDivFlashU64 (sum : WordSum) : UInt64 :=
  if sum.highCarry then
    let foldedRem := (sum.lowWord % flashDenom) + u64ModFlashRem
    u64ModFlashQuot + (sum.lowWord / flashDenom) + ((foldedRem + flashMaxRem) / flashDenom)
  else
    let biased := sum.lowWord + flashMaxRem
    if biased < sum.lowWord then
      (sum.lowWord / flashDenom) + (((sum.lowWord % flashDenom) + flashMaxRem) / flashDenom)
    else
      biased / flashDenom

end LeanModel.WordMath
