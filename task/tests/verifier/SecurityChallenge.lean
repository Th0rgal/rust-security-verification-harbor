import Lean

namespace SecurityChallenge

def u64Max : Nat := 18446744073709551615

-- Opaque implementation plus a kernel-checked contract, exposed by projection.
private opaque certifiedAuthorizer :
    {f : Nat → Nat → Nat → Option Nat //
      ∀ balance amount fee, f balance amount fee =
        if amount + fee ≤ u64Max ∧ amount + fee ≤ balance
        then some (amount + fee) else none} :=
  ⟨fun balance amount fee =>
      if amount + fee ≤ u64Max ∧ amount + fee ≤ balance
      then some (amount + fee) else none, by intros; rfl⟩

noncomputable def repairedAuthorize (balance amount fee : Nat) : Option Nat :=
  certifiedAuthorizer.val balance amount fee

theorem repairedAuthorize_success (balance amount fee total : Nat) :
    repairedAuthorize balance amount fee = some total ↔
      total = amount + fee ∧ amount + fee ≤ u64Max ∧ amount + fee ≤ balance := by
  unfold repairedAuthorize
  rw [certifiedAuthorizer.property]
  by_cases allowed : amount + fee ≤ u64Max ∧ amount + fee ≤ balance
  · simp only [if_pos allowed, Option.some.injEq]
    constructor
    · intro h; exact ⟨h.symm, allowed⟩
    · intro h; exact h.1.symm
  · simp [allowed]

end SecurityChallenge
