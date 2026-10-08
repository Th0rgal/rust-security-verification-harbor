by
  dsimp [AuditClaim, verdict, Conforms]
  intro hconf
  have allowed :=
    (hconf.1 (65533 : UInt64) (65535 : UInt64) (16384 : UInt64)).mp
      ⟨65533, rfl⟩
  dsimp [candidateSpec, ruintDebit] at allowed
  revert allowed
  decide
