import Lean
import LeanModel.Constants
import LeanModel.WordMath
import LeanModel.ReciprocalDiv
import LeanModel.BroadwordSwar
import LeanModel.MontgomeryField
import LeanModel.GoldilocksField
import LeanModel.FeeSchedule
import LeanModel.LiquidityPool
import LeanModel.TranscriptCodec

namespace LeanModel.ClearingPipeline

open LeanModel.Constants
open LeanModel.WordMath
open LeanModel.ReciprocalDiv
open LeanModel.BroadwordSwar
open LeanModel.MontgomeryField
open LeanModel.GoldilocksField
open LeanModel.FeeSchedule
open LeanModel.LiquidityPool
open LeanModel.TranscriptCodec

structure ClearingBreakdown where
  netBpsFee : UInt64
  flashLpFee : UInt64
  blobSlotQuotient : UInt64
  calldataSurcharge : UInt64
  proverLevy : UInt64
  domainSurcharge : UInt64
  baseSurcharge : UInt64
  bridgeSurcharge : UInt64

structure ClearingTicket where
  principal : UInt64
  netBpsFee : UInt64
  flashLpFee : UInt64
  blobSlotQuotient : UInt64
  calldataSurcharge : UInt64
  proverLevy : UInt64
  domainSurcharge : UInt64
  bridgeSurcharge : UInt64
  totalSurcharge : UInt64
  totalDebit : UInt64

def computeClearingBreakdown (amount fee : UInt64) : ClearingBreakdown :=
  let notionalSum : WordSum := addU64WithCarry amount fee
  let feeQuote : FeeQuote := evaluateSettlementFee notionalSum
  let flashQuote : PoolReserveQuote := quoteFlashLpRetention amount fee
  let blobQuote : BlobSlotQuote := quoteBlobGasSlots amount fee
  let laneQuote : CalldataLaneQuote := quoteCalldataLaneSurcharge fee
  let levyQuote : ProverLevyQuote := quoteProverTranscriptLevy amount fee
  let bridgeQuote : GoldilocksQuote := quoteBridgeVerifierFee amount fee
  let domainSurcharge : UInt64 := decodeDomainTag fee
  let netBpsFee : UInt64 := feeQuote.netFee
  let flashLpFee : UInt64 := flashQuote.lpRetention
  let blobSlotQuotient : UInt64 := blobQuote.slotQuotient
  let calldataSurcharge : UInt64 := laneQuote.surcharge
  let proverLevy : UInt64 := levyQuote.proverLevy
  let bridgeSurcharge : UInt64 := bridgeQuote.bridgeFee
  let baseSurcharge : UInt64 :=
    netBpsFee + flashLpFee + blobSlotQuotient + calldataSurcharge + proverLevy + domainSurcharge
  {
    netBpsFee := netBpsFee
    flashLpFee := flashLpFee
    blobSlotQuotient := blobSlotQuotient
    calldataSurcharge := calldataSurcharge
    proverLevy := proverLevy
    domainSurcharge := domainSurcharge
    baseSurcharge := baseSurcharge
    bridgeSurcharge := bridgeSurcharge
  }

def assembleClearingTicket (amount : UInt64) (breakdown : ClearingBreakdown) : Option ClearingTicket :=
  if breakdown.bridgeSurcharge ≤ u64Max - breakdown.baseSurcharge then
    let totalSurcharge : UInt64 := breakdown.baseSurcharge + breakdown.bridgeSurcharge
    if totalSurcharge ≤ u64Max - amount then
      some {
        principal := amount
        netBpsFee := breakdown.netBpsFee
        flashLpFee := breakdown.flashLpFee
        blobSlotQuotient := breakdown.blobSlotQuotient
        calldataSurcharge := breakdown.calldataSurcharge
        proverLevy := breakdown.proverLevy
        domainSurcharge := breakdown.domainSurcharge
        bridgeSurcharge := breakdown.bridgeSurcharge
        totalSurcharge := totalSurcharge
        totalDebit := amount + totalSurcharge
      }
    else
      none
  else
    none

def quoteClearingTicket (amount fee : UInt64) : Option ClearingTicket :=
  let breakdown : ClearingBreakdown := computeClearingBreakdown amount fee
  assembleClearingTicket amount breakdown

def commitClearingTicket (balance : UInt64) (ticket : ClearingTicket) : Option UInt64 :=
  if ticket.totalDebit ≤ balance then
    some ticket.totalDebit
  else
    none

def previewRemainingBalance (balance : UInt64) (ticket : ClearingTicket) : UInt64 :=
  if ticket.totalDebit ≤ balance then
    balance - ticket.totalDebit
  else
    0

def verifyTicketConservation (ticket : ClearingTicket) : Bool :=
  let recomputedBase : UInt64 :=
    ticket.netBpsFee + ticket.flashLpFee + ticket.blobSlotQuotient +
      ticket.calldataSurcharge + ticket.proverLevy + ticket.domainSurcharge
  decide (recomputedBase + ticket.bridgeSurcharge = ticket.totalSurcharge ∧
    ticket.principal + ticket.totalSurcharge = ticket.totalDebit)

def authorizeBreakdown (balance amount : UInt64) (breakdown : ClearingBreakdown) : Option UInt64 :=
  if breakdown.bridgeSurcharge ≤ u64Max - breakdown.baseSurcharge then
    let totalSurcharge : UInt64 := breakdown.baseSurcharge + breakdown.bridgeSurcharge
    if totalSurcharge ≤ u64Max - amount then
      let totalDebit : UInt64 := amount + totalSurcharge
      if totalDebit ≤ balance then
        some totalDebit
      else
        none
    else
      none
  else
    none

def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  authorizeBreakdown balance amount (computeClearingBreakdown amount fee)

end LeanModel.ClearingPipeline
