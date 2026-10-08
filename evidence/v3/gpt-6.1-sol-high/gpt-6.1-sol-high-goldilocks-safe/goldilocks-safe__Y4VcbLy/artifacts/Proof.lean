by
  unfold AuditClaim verdict
  constructor
  · intro b a f
    change (∃ t, challengeAuthorize b a f = some t) ↔ exactDebit a f ≤ b.toNat
    constructor
    · rintro ⟨t, ht⟩
      exact ((authorization_correct b a f t).mp ht).1
    · intro h
      have hb := b.toNat_lt
      have hd : exactDebit a f < 2 ^ 64 := by omega
      refine ⟨UInt64.ofNat (exactDebit a f), ?_⟩
      apply (authorization_correct b a f _).mpr
      exact ⟨h, UInt64.toNat_ofNat_of_lt' hd⟩
  · intro b a f t ht
    exact (authorization_correct b a f t).mp ht
