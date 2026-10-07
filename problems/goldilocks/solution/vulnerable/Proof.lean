by
  intro h
  have allowed :=
    (h.1 (18446744069414584318 : UInt64) (0 : UInt64) (8589934592 : UInt64)).mp
      ⟨4294967293, rfl⟩
  dsimp [candidateSpec, goldilocksDebit] at allowed
  revert allowed
  decide
