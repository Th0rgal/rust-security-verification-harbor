by
  intro h
  have hrun : challengeAuthorize 128 0 128 = some 128 := by decide
  have hout := h.2 128 0 128 128 hrun
  revert hout
  show ¬ (CandidateSpecDefs.debit 0 128 ≤ (128 : UInt64).toNat ∧ (128 : UInt64).toNat = CandidateSpecDefs.debit 0 128)
  decide
