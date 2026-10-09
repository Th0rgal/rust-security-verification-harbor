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
open LeanModel.FeeSchedule

structure ClearingBreakdown where
  netBpsFee : UInt64
  blobSlotQuotient : UInt64
  calldataSurcharge : UInt64
  proverLevy : UInt64
  totalSurcharge : UInt64

structure ClearingTicket where
  principal : UInt64
  netBpsFee : UInt64
  blobSlotQuotient : UInt64
  calldataSurcharge : UInt64
  proverLevy : UInt64
  totalSurcharge : UInt64
  totalDebit : UInt64

def laneCharge (x : UInt64) : UInt64 :=
  let byte := x % 256
  if byte = 0 then 0 else 256 + byte

def protocolGross (amount fee : UInt64) : UInt64 :=
  amount / 10000 + fee / 10000 + (amount % 10000 + fee % 10000 + 9999) / 10000

def blobCharge (amount fee : UInt64) : UInt64 :=
  ((fee % 32771) * 65536 + amount % 65536) / 32771

def calldataCharge (fee : UInt64) : UInt64 :=
  laneCharge fee + laneCharge (fee / 256) + laneCharge (fee / 65536)
  + laneCharge (fee / 16777216) + laneCharge (fee / 4294967296)
  + laneCharge (fee / 1099511627776) + laneCharge (fee / 281474976710656)
  + laneCharge (fee / 72057594037927936)

def levyCharge (amount fee : UInt64) : UInt64 :=
  (((amount % 4294967296) % 2013265921) * 943718400
    + fee % 2013265921) % 2013265921

def computeClearingBreakdown (amount fee : UInt64) : ClearingBreakdown :=
  let gross := protocolGross amount fee
  let net := gross - gross / 10
  let blob := blobCharge amount fee
  let calldata := calldataCharge fee
  let levy := levyCharge amount fee
  { netBpsFee := net
    blobSlotQuotient := blob
    calldataSurcharge := calldata
    proverLevy := levy
    totalSurcharge := net + blob + calldata + levy }

def assembleClearingTicket (amount : UInt64) (breakdown : ClearingBreakdown) : Option ClearingTicket :=
  if breakdown.totalSurcharge ≤ u64Max - amount then
    some {
      principal := amount
      netBpsFee := breakdown.netBpsFee
      blobSlotQuotient := breakdown.blobSlotQuotient
      calldataSurcharge := breakdown.calldataSurcharge
      proverLevy := breakdown.proverLevy
      totalSurcharge := breakdown.totalSurcharge
      totalDebit := amount + breakdown.totalSurcharge
    }
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
  let recomputed : UInt64 :=
    ticket.netBpsFee + ticket.blobSlotQuotient + ticket.calldataSurcharge + ticket.proverLevy
  decide (recomputed = ticket.totalSurcharge ∧ ticket.principal + ticket.totalSurcharge = ticket.totalDebit)

def authorizeBreakdown (balance amount : UInt64) (breakdown : ClearingBreakdown) : Option UInt64 :=
  if breakdown.totalSurcharge ≤ u64Max - amount then
    let totalDebit : UInt64 := amount + breakdown.totalSurcharge
    if totalDebit ≤ balance then
      some totalDebit
    else
      none
  else
    none

def challengeAuthorize (balance amount fee : UInt64) : Option UInt64 :=
  authorizeBreakdown balance amount (computeClearingBreakdown amount fee)

end LeanModel.ClearingPipeline
