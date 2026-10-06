by
  intro h
  have h1 : challengeAuthorize 1660206966633859 0 18446744073709541617 = some 1660206966633859 := by
    decide
  have h2 := (h.1 1660206966633859 0 18446744073709541617).mp ⟨_, h1⟩
  revert h2
  show ¬ (policyTotal 0 18446744073709541617 ≤ (1660206966633859 : UInt64).toNat)
  decide
