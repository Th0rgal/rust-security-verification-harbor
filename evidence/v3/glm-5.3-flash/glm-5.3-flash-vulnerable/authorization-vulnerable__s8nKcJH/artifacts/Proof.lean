by
  intro conforms
  obtain ⟨hiff, _⟩ := conforms
  have hmodel :
      SecurityChallenge.challengeAuthorize
        18446744073709551615 18446744073709551615 1 = some 0 := by
    unfold SecurityChallenge.challengeAuthorize
    simp
  have haccepted : candidateSpec.accepts
      18446744073709551615 18446744073709551615 1 :=
    (hiff 18446744073709551615 18446744073709551615 1).mp ⟨0, hmodel⟩
  unfold candidateSpec at haccepted
  have hbalance :
      (18446744073709551615 : UInt64).toNat = 18446744073709551615 := rfl
  have hamount :
      (18446744073709551615 : UInt64).toNat = 18446744073709551615 := rfl
  have hfee : (1 : UInt64).toNat = 1 := rfl
  omega
