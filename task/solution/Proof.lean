by
  intro h
  have allowed := (h.1 (0 : UInt64) (18446744073709551615 : UInt64) (1 : UInt64)).mp
    ⟨0, by decide⟩
  change (18446744073709551615 : UInt64).toNat + (1 : UInt64).toNat ≤ (0 : UInt64).toNat at allowed
  exact (by decide : ¬ ((18446744073709551615 : UInt64).toNat + (1 : UInt64).toNat ≤ (0 : UInt64).toNat)) allowed
