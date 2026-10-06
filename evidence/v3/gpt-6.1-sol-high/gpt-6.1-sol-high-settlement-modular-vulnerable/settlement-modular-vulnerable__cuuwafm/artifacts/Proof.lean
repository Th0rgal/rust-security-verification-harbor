by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro conforms
  have actual : SecurityChallenge.challengeAuthorize
      (1660206966633859 : UInt64) (0 : UInt64)
      (18446744073709549616 : UInt64) = some (1660206966633859 : UInt64) := by
    decide
  have accepted := (conforms.1 (1660206966633859 : UInt64) (0 : UInt64)
    (18446744073709549616 : UInt64)).mp ⟨_, actual⟩
  have rejected : ¬ candidateSpec.accepts (1660206966633859 : UInt64)
      (0 : UInt64) (18446744073709549616 : UInt64) := by
    change ¬ ((1660206966633860 : Nat) ≤ 1660206966633859)
    decide
  exact rejected accepted
