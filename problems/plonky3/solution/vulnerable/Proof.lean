by
  intro h
  have allowed :=
    (h.1 (4294967297 : UInt64) (4294967297 : UInt64) (1069547520 : UInt64)).mp
      ⟨4294967297, rfl⟩
  dsimp [candidateSpec, plonky3Debit] at allowed
  revert allowed
  decide
