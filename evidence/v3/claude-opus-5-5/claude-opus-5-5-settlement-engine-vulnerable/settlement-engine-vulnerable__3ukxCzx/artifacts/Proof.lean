by
  intro h
  have hrun : challengeAuthorize 1660206966633859 0 18446744073709549616 = some 1660206966633859 := by
    decide
  have h1 := h.2 1660206966633859 0 18446744073709549616 1660206966633859 hrun
  have h2 : (1660206966633859 : UInt64).toNat = specTotalDebit 0 18446744073709549616 := h1
  revert h2
  unfold specTotalDebit specRebate specGrossFee
  decide
