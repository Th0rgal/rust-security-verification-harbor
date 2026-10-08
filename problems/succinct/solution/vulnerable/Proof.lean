by
  dsimp [AuditClaim, verdict, Conforms]
  intro hconf
  have h_call : challengeAuthorize 200 0 128 = some 128 := by
    decide
  have hout := hconf.2 200 0 128 128 h_call
  dsimp [candidateSpec, succinctDebit, isNz] at hout
  revert hout
  decide
