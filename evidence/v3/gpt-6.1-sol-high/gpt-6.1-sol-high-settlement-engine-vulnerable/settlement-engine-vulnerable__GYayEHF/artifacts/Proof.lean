by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro conforms
  have actual : SecurityChallenge.challengeAuthorize
      1660206966633859 0 18446744073709541617 = some 1660206966633859 := by
    decide
  have unaffordable : ¬ candidateSpec.accepts
      1660206966633859 0 18446744073709541617 := by
    unfold candidateSpec settlementDebit
    decide
  exact unaffordable ((conforms.1 1660206966633859 0 18446744073709541617).mp
    ⟨1660206966633859, actual⟩)
