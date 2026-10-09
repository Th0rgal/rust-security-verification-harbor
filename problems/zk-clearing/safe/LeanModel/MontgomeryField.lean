import Lean
import LeanModel.Constants

namespace LeanModel.MontgomeryField

open LeanModel.Constants

structure ProverLevyQuote where
  packedTranscript : UInt64
  montyT : UInt64
  proverLevy : UInt64

def packTranscript (amount fee : UInt64) : UInt64 :=
  (amount % limbBase) + (fee % babyBearP) * limbBase

def montyQuotient (x : UInt64) : UInt64 :=
  ((x % limbBase) * babyBearMu) % limbBase

def montyReduce (x : UInt64) : UInt64 :=
  let t : UInt64 := montyQuotient x
  let u : UInt64 := babyBearP * t
  let diff : UInt64 := x - u
  let hi : UInt64 := diff / limbBase
  if x < u then
    babyBearP + hi - limbBase
  else
    hi

def montyMulBabyBear (a b : UInt64) : UInt64 :=
  let prod : UInt64 := (a % babyBearP) * (b % babyBearP)
  montyReduce prod

def canonicalAddBabyBear (a b : UInt64) : UInt64 :=
  let sum : UInt64 := a + b
  if babyBearP ≤ sum then
    sum - babyBearP
  else
    sum

def canonicalSubBabyBear (a b : UInt64) : UInt64 :=
  if b ≤ a then
    a - b
  else
    (a + babyBearP) - b

def quoteProverTranscriptLevy (amount fee : UInt64) : ProverLevyQuote :=
  let packedTranscript : UInt64 := packTranscript amount fee
  let montyT : UInt64 := montyQuotient packedTranscript
  let proverLevy : UInt64 := montyReduce packedTranscript
  {
    packedTranscript := packedTranscript
    montyT := montyT
    proverLevy := proverLevy
  }

end LeanModel.MontgomeryField
