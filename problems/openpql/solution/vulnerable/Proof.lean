by
  intro h
  have allowed :=
    (h.1 (1 : UInt64) (2 : UInt64) (18446744073709551615 : UInt64)).mp
      ⟨1, rfl⟩
  dsimp [candidateSpec, openpqlDebit] at allowed
  revert allowed
  decide
