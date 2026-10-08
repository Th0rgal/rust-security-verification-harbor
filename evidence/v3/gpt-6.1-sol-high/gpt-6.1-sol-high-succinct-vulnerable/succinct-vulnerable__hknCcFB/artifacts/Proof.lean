by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro h
  have actual : SecurityChallenge.challengeAuthorize 128 0 128 = some 128 := by
    decide
  have rejected : ¬ candidateSpec.accepts 128 0 128 := by
    change ¬ ((384 : Nat) ≤ 128)
    decide
  exact rejected ((h.1 128 0 128).mp ⟨128, actual⟩)
