by
  intro h
  have allowed :=
    (h.1 (1660206966635476 : UInt64) (1617 : UInt64) (18446744073709540000 : UInt64)).mp
      ⟨1660206966635476, rfl⟩
  dsimp [candidateSpec] at allowed
  revert allowed
  decide
