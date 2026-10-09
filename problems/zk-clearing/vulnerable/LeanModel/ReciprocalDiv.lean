import Lean
import LeanModel.Constants
import LeanModel.WordMath

namespace LeanModel.ReciprocalDiv

open LeanModel.Constants
open LeanModel.WordMath

structure BlobSlotQuote where
  highLimb : UInt64
  lowLimb : UInt64
  slotQuotient : UInt64
  slotRemainder : UInt64

def div2x1Mg10 (u1 u0 : UInt64) : UInt64 :=
  let qFull : UInt64 := (u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)
  let q1 : UInt64 := qFull >>> 16
  let q0 : UInt64 := qFull &&& limbMask
  let r : UInt64 := (subBias + u0 - q1 * mg10Divisor) &&& limbMask
  let (qCorr, rCorr) :=
    if q0 < r then
      (q1 - 1, (r + mg10Divisor) &&& limbMask)
    else
      (q1, r)
  if mg10Divisor ≤ rCorr then
    qCorr + 1
  else
    qCorr

def rem2x1Mg10 (u1 u0 quot : UInt64) : UInt64 :=
  let dividend : UInt64 := (u1 <<< 16) + u0
  dividend - (quot * mg10Divisor)

def quoteBlobGasSlots (amount fee : UInt64) : BlobSlotQuote :=
  let highLimb : UInt64 := fee % mg10Divisor
  let lowLimb : UInt64 := extractLowU16 amount
  let slotQuotient : UInt64 := div2x1Mg10 highLimb lowLimb
  let slotRemainder : UInt64 := rem2x1Mg10 highLimb lowLimb slotQuotient
  {
    highLimb := highLimb
    lowLimb := lowLimb
    slotQuotient := slotQuotient
    slotRemainder := slotRemainder
  }

def verifyBlobSlotEuclidean (quote : BlobSlotQuote) : Bool :=
  let dividend : UInt64 := (quote.highLimb <<< 16) + quote.lowLimb
  let reconstructed : UInt64 := (quote.slotQuotient * mg10Divisor) + quote.slotRemainder
  decide (quote.slotRemainder < mg10Divisor ∧ reconstructed = dividend)

def estimateBlobGasUnits (quote : BlobSlotQuote) : UInt64 :=
  quote.slotQuotient * blobGasPerSlot

def ceilBlobSlots (quote : BlobSlotQuote) : UInt64 :=
  if 0 < quote.slotRemainder then
    quote.slotQuotient + 1
  else
    quote.slotQuotient

end LeanModel.ReciprocalDiv
