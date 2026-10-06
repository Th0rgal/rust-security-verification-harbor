by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro conformity
  have accepted : SecurityChallenge.challengeAuthorize
      (1660206966633859 : UInt64) (0 : UInt64)
      (18446744073709549999 : UInt64) = some (1660206966633859 : UInt64) := by
    decide
  have affordable := (conformity.1
    (1660206966633859 : UInt64) (0 : UInt64)
    (18446744073709549999 : UInt64)).mp ⟨_, accepted⟩
  have unaffordable : ¬ candidateSpec.accepts
      (1660206966633859 : UInt64) (0 : UInt64)
      (18446744073709549999 : UInt64) := by
    dsimp only [candidateSpec, settlementDebit, settlementGrossFee]
    decide
  exact unaffordable affordable
