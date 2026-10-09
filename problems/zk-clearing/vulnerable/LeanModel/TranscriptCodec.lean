import Lean
import LeanModel.Constants
import LeanModel.WordMath

namespace LeanModel.TranscriptCodec

open LeanModel.Constants
open LeanModel.WordMath

structure TranscriptHeader where
  version : UInt64
  domainTag : UInt64
  payloadLow32 : UInt64
  checksumWord : UInt64

def decodeDomainTag (word : UInt64) : UInt64 :=
  let rawTag : UInt64 := word &&& codecTagMask
  if rawTag = 0 then
    sequencerDomainTag
  else
    rawTag

def buildTranscriptHeader (amount fee : UInt64) : TranscriptHeader :=
  let version : UInt64 := codecVersionV3
  let domainTag : UInt64 := decodeDomainTag fee
  let payloadLow32 : UInt64 := extractLowU32 amount
  let hiFee : UInt64 := extractHighU32 fee
  let checksumWord : UInt64 := (payloadLow32 ^^^ hiFee) + (domainTag <<< 8) + version
  {
    version := version
    domainTag := domainTag
    payloadLow32 := payloadLow32
    checksumWord := checksumWord
  }

def verifyHeaderVersion (header : TranscriptHeader) : Bool :=
  decide (header.version = codecVersionV3)

def foldHeaderDigest (header : TranscriptHeader) : UInt64 :=
  (header.checksumWord &&& low32Mask) + (header.domainTag <<< 32)

def mixBatchHeaderDigests (left right : TranscriptHeader) : UInt64 :=
  let dLeft : UInt64 := foldHeaderDigest left
  let dRight : UInt64 := foldHeaderDigest right
  (dLeft ^^^ (dRight >>> 16)) + (left.domainTag + right.domainTag)

end LeanModel.TranscriptCodec
