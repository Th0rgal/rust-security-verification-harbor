import Lean
import LeanModel.Constants

namespace LeanModel.BroadwordSwar

open LeanModel.Constants

structure CalldataLaneQuote where
  activeLanes : UInt64
  byteWeightSum : UInt64
  surcharge : UInt64

def uNz8 (x : UInt64) : UInt64 :=
  (((x ||| h8Mask) - l8Mask) ||| x) &&& h8Mask

def countNzBytes (x : UInt64) : UInt64 :=
  (((uNz8 x) >>> 7) * l8Mask) >>> 56

def countZeroBytesSwar (x : UInt64) : UInt64 :=
  8 - countNzBytes x

def hasHighBitByte (x : UInt64) : Bool :=
  decide ((x &&& h8Mask) != 0)

def sumBytes (x : UInt64) : UInt64 :=
  let pairSum : UInt64 := (x &&& m16Mask) + ((x >>> 8) &&& m16Mask)
  ((pairSum * l16Mask) >>> 48) &&& limbMask

def sumEvenBytesSwar (x : UInt64) : UInt64 :=
  let evenLanes : UInt64 := x &&& m16Mask
  ((evenLanes * l16Mask) >>> 48) &&& limbMask

def sumOddBytesSwar (x : UInt64) : UInt64 :=
  let oddLanes : UInt64 := (x >>> 8) &&& m16Mask
  ((oddLanes * l16Mask) >>> 48) &&& limbMask

def quoteCalldataLaneSurcharge (fee : UInt64) : CalldataLaneQuote :=
  let activeLanes : UInt64 := countNzBytes fee
  let byteWeightSum : UInt64 := sumBytes fee
  let surcharge : UInt64 := (activeLanes <<< calldataNzByteShift) + byteWeightSum
  {
    activeLanes := activeLanes
    byteWeightSum := byteWeightSum
    surcharge := surcharge
  }

end LeanModel.BroadwordSwar
