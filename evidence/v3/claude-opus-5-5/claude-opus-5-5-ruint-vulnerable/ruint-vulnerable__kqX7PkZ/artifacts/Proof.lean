by
  intro h
  have hacc : candidateSpec.accepts 65532 65533 16384 :=
    (h.1 65532 65533 16384).mp ⟨65532, by decide⟩
  have hnot : ¬ (intendedDebit 65533 16384 ≤ (65532 : UInt64).toNat) := by
    unfold intendedDebit
    decide
  exact hnot hacc
