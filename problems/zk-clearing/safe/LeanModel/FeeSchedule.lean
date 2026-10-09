import Lean
import LeanModel.Constants
import LeanModel.WordMath

namespace LeanModel.FeeSchedule

open LeanModel.Constants
open LeanModel.WordMath

structure FeeSchedule where
  bpsDenom : UInt64
  rebateDivisor : UInt64
  makerCapDivisor : UInt64

structure FeeQuote where
  grossFee : UInt64
  rebate : UInt64
  netFee : UInt64

def defaultSchedule : FeeSchedule :=
  {
    bpsDenom := bpsDenom
    rebateDivisor := rebateDivisor
    makerCapDivisor := makerRebateCapDivisor
  }

def computeTierRebate (grossFee : UInt64) : UInt64 :=
  grossFee / rebateDivisor

def computeCappedMakerRebate (grossFee capBasis : UInt64) : UInt64 :=
  let baseRebate : UInt64 := grossFee / rebateDivisor
  let maxRebate : UInt64 := capBasis / makerRebateCapDivisor
  if baseRebate ≤ maxRebate then baseRebate else maxRebate

def evaluateSettlementFee (sum : WordSum) : FeeQuote :=
  let grossFee : UInt64 := ceilDivBpsU64 sum
  let rebate : UInt64 := computeTierRebate grossFee
  let netFee : UInt64 := grossFee - rebate
  {
    grossFee := grossFee
    rebate := rebate
    netFee := netFee
  }

def evaluatePassiveFloorFee (sum : WordSum) : FeeQuote :=
  let grossFee : UInt64 := floorDivBpsU64 sum
  let rebate : UInt64 := computeTierRebate grossFee
  let netFee : UInt64 := grossFee - rebate
  {
    grossFee := grossFee
    rebate := rebate
    netFee := netFee
  }

def computeFeeRoundingSpread (sum : WordSum) : UInt64 :=
  let ceilQ : FeeQuote := evaluateSettlementFee sum
  let floorQ : FeeQuote := evaluatePassiveFloorFee sum
  ceilQ.netFee - floorQ.netFee

def classifySettlementTier (sum : WordSum) : UInt64 :=
  if !sum.highCarry && sum.lowWord == 0 then
    0
  else if isInstitutionalNotional sum then
    2
  else
    1

end LeanModel.FeeSchedule
