by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro h
  have actual : SecurityChallenge.challengeAuthorize 1 2 18446744073709551615 = some 1 := by
    decide
  have claimed := h.2 1 2 18446744073709551615 1 actual
  have wrong : ¬ candidateSpec.output 1 2 18446744073709551615 1 := by
    unfold candidateSpec policyDebit policyIndex policyDigit policyClamp
    decide
  exact wrong claimed
