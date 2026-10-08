by
  intro h
  have allowed :=
    (h.1 (18446744073709551615 : UInt64) (18446744073708551617 : UInt64) (999999 : UInt64)).mp
      ⟨9223372036854275808, rfl⟩
  dsimp [candidateSpec, whirlpoolDebit] at allowed
  revert allowed
  decide
