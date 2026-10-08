fun h => by
  have hrun : challengeAuthorize 1 2 18446744073709551615 = some 1 := by decide
  have hacc := (h.1 1 2 18446744073709551615).mp ⟨1, hrun⟩
  have hnot : ¬ (policyTotal 2 18446744073709551615 ≤ (1 : UInt64).toNat) := by decide
  exact hnot hacc
