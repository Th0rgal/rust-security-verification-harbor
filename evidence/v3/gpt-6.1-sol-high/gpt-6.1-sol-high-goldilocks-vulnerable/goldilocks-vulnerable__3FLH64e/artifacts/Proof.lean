by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro h
  have accepted : SecurityChallenge.challengeAuthorize 4294967294 0 4294967296 =
      some 4294967294 := by decide
  have unaffordable : ¬ candidateSpec.accepts 4294967294 0 4294967296 := by
    unfold candidateSpec policyDebit
    decide
  exact unaffordable ((h.1 4294967294 0 4294967296).mp ⟨4294967294, accepted⟩)
