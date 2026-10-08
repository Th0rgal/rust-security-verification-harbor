fun h => by
  have hrun : challengeAuthorize 4294967294 0 4294967296 = some 4294967294 := by decide
  have h2 := h.2 4294967294 0 4294967296 4294967294 hrun
  have h3 : ¬ ((4294967294 : UInt64).toNat = (0 : UInt64).toNat / 2 + ((0 : UInt64).toNat + (4294967296 : UInt64).toNat * 18446744073709551616) % 18446744069414584321) := by decide
  exact h3 h2
