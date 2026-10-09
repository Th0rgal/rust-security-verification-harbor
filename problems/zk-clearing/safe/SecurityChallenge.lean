import Lean
import LeanModel.ClearingPipeline

namespace SecurityChallenge

export LeanModel.Constants (
  bpsDenom bpsMaxRem u64ModBpsQuot u64ModBpsRem rebateDivisor
  makerRebateCapDivisor treasuryCutDivisor flashDenom flashMaxRem
  u64ModFlashQuot u64ModFlashRem institutionalBandMin
  mg10Divisor mg10Reciprocal limbMask subBias blobGasPerSlot
  l8Mask h8Mask m16Mask l16Mask calldataNzByteShift
  babyBearP babyBearMu limbBase low32Mask
  goldilocksP goldilocksEps
  codecTagMask codecVersionV3 sequencerDomainTag
  u64Max
)
export LeanModel.WordMath (
  WordSum WordDiff addU64WithCarry subU64WithBorrow
  extractLowU16 extractLowU32 extractHighU32 packU32Limbs
  isInstitutionalNotional remBpsU64 floorDivBpsU64 ceilDivBpsU64
  floorDivFlashU64 ceilDivFlashU64
)
export LeanModel.ReciprocalDiv (
  BlobSlotQuote div2x1Mg10 rem2x1Mg10 quoteBlobGasSlots
  verifyBlobSlotEuclidean estimateBlobGasUnits ceilBlobSlots
)
export LeanModel.BroadwordSwar (
  CalldataLaneQuote uNz8 countNzBytes countZeroBytesSwar
  hasHighBitByte sumBytes sumEvenBytesSwar sumOddBytesSwar
  quoteCalldataLaneSurcharge
)
export LeanModel.MontgomeryField (
  ProverLevyQuote packTranscript montyQuotient montyReduce
  montyMulBabyBear canonicalAddBabyBear canonicalSubBabyBear
  quoteProverTranscriptLevy
)
export LeanModel.GoldilocksField (
  GoldilocksQuote reduceGoldilocksStep1 reduceGoldilocks128
  canonicalizeGoldilocksU64 addGoldilocksMod subGoldilocksMod
  foldGoldilocksChallenge quoteBridgeVerifierFee
)
export LeanModel.FeeSchedule (
  FeeSchedule FeeQuote defaultSchedule computeTierRebate
  computeCappedMakerRebate evaluateSettlementFee evaluatePassiveFloorFee
  computeFeeRoundingSpread classifySettlementTier
)
export LeanModel.LiquidityPool (
  PoolReserveQuote FlashLoanReceipt splitPoolReserve quoteLpRetention
  assessFlashFeeCeil quoteFlashLpRetention assessFlashFeeFloor quoteFlashRepayment
  checkPoolReserveSolvency
)
export LeanModel.TranscriptCodec (
  TranscriptHeader decodeDomainTag buildTranscriptHeader
  verifyHeaderVersion foldHeaderDigest mixBatchHeaderDigests
)
export LeanModel.ClearingPipeline (
  ClearingBreakdown ClearingTicket computeClearingBreakdown
  assembleClearingTicket quoteClearingTicket commitClearingTicket
  previewRemainingBalance verifyTicketConservation authorizeBreakdown
  challengeAuthorize
)

structure AuthorizationSpec where
  accepts : UInt64 → UInt64 → UInt64 → Prop
  output : UInt64 → UInt64 → UInt64 → UInt64 → Prop

inductive AuditVerdict where
  | vulnerable
  | safe
  deriving Repr

def Conforms (spec : AuthorizationSpec)
    (authorize : UInt64 → UInt64 → UInt64 → Option UInt64) : Prop :=
  (∀ b a f, (∃ total, authorize b a f = some total) ↔ spec.accepts b a f) ∧
  (∀ b a f total, authorize b a f = some total → spec.output b a f total)

def AuditClaim (spec : AuthorizationSpec) (_verdict : AuditVerdict) : Prop :=
  Conforms spec challengeAuthorize

end SecurityChallenge
