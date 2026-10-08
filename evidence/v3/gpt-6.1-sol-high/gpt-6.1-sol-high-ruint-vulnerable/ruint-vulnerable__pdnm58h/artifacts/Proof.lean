by
  change ¬ SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  intro h
  have run : SecurityChallenge.challengeAuthorize 65533 65534 16384 = some 65533 := by
    decide
  have required := h.2 65533 65534 16384 65533 run
  have impossible : ¬ candidateSpec.output 65533 65534 16384 65533 := by
    unfold candidateSpec settlementDebit
    decide
  exact impossible required
