by
  change ¬ Conforms candidateSpec challengeAuthorize
  intro h
  have accepted : challengeAuthorize 9223372036854275808 18446744073708551617 999999 = some 9223372036854275808 := by
    decide
  have rejected : ¬ candidateSpec.accepts 9223372036854275808 18446744073708551617 999999 := by
    change ¬ settlementDebit 18446744073708551617 999999 ≤ (9223372036854275808 : UInt64).toNat
    decide
  exact rejected ((h.1 9223372036854275808 18446744073708551617 999999).mp ⟨9223372036854275808, accepted⟩)
