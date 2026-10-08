by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro h
  have accepted : SecurityChallenge.challengeAuthorize 1 1 1069547520 = some 1 := by
    decide
  have mustAccept : candidateSpec.accepts 1 1 1069547520 :=
    (h.1 1 1 1069547520).mp ⟨1, accepted⟩
  have unaffordable : ¬ candidateSpec.accepts 1 1 1069547520 := by
    unfold candidateSpec policyDebit
    decide
  exact unaffordable mustAccept
