import Lean
import LeanModel.Constants
import LeanModel.WordMath
import LeanModel.FeeSchedule

namespace LeanModel.LiquidityPool

open LeanModel.Constants
open LeanModel.WordMath
open LeanModel.FeeSchedule

structure PoolReserveQuote where
  treasuryCut : UInt64
  lpRetention : UInt64

structure FlashLoanReceipt where
  principal : UInt64
  flashLevy : UInt64
  totalRepayment : UInt64

def splitPoolReserve (quote : FeeQuote) : PoolReserveQuote :=
  let treasuryCut : UInt64 := quote.netFee / treasuryCutDivisor
  let lpRetention : UInt64 := quote.netFee - treasuryCut
  {
    treasuryCut := treasuryCut
    lpRetention := lpRetention
  }

def quoteLpRetention (quote : FeeQuote) : UInt64 :=
  (splitPoolReserve quote).lpRetention

def assessFlashFeeCeil (principal surcharge : UInt64) : UInt64 :=
  let sum := addU64WithCarry principal surcharge
  ceilDivFlashU64 sum

def assessFlashFeeFloor (principal surcharge : UInt64) : UInt64 :=
  let sum := addU64WithCarry principal surcharge
  floorDivFlashU64 sum

def quoteFlashRepayment (principal surcharge : UInt64) : Option FlashLoanReceipt :=
  let flashLevy : UInt64 := assessFlashFeeCeil principal surcharge
  if flashLevy ≤ u64Max - principal then
    some {
      principal := principal
      flashLevy := flashLevy
      totalRepayment := principal + flashLevy
    }
  else
    none

def checkPoolReserveSolvency (currentReserve : UInt64) (quote : FeeQuote) (minReserve : UInt64) : Bool :=
  let lpShare : UInt64 := quoteLpRetention quote
  if lpShare ≤ u64Max - currentReserve then
    decide (minReserve ≤ currentReserve + lpShare)
  else
    true

end LeanModel.LiquidityPool
