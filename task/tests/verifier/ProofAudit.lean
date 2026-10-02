import SecurityChallenge
import Lean

open Lean SecurityChallenge

-- Trusted fixed type. Candidate is loaded as data only, never as executable
-- metaprogram extensions or initializers.
theorem expectedAuthorizeSound (balance amount fee total : Nat)
    (h : repairedAuthorize balance amount fee = some total) :
    amount + fee = total ∧ total ≤ balance := by
  obtain ⟨hTotal, _, hBalance⟩ :=
    (repairedAuthorize_success balance amount fee total).mp h
  subst total
  exact ⟨rfl, hBalance⟩

partial def axiomClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (axioms : NameSet := {}) : NameSet :=
  match todo with
  | [] => axioms
  | name :: rest =>
    if seen.contains name then axiomClosure env rest seen axioms
    else
      let seen := seen.insert name
      match env.find? name with
      | none => axiomClosure env rest seen (axioms.insert name)
      | some ci =>
        let deps := ci.type.getUsedConstants.toList ++
          (match ci.value? true with | some v => v.getUsedConstants.toList | none => [])
        let axioms := if ci.isAxiom then axioms.insert name else axioms
        axiomClosure env (deps ++ rest) seen axioms

unsafe def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{module := `ProofAudit}, {module := `Candidate}] {} fun env => do
    let some candidate := env.find? `patched_authorize_sound
      | throw <| IO.userError "candidate theorem missing"
    let some expected := env.find? `expectedAuthorizeSound
      | throw <| IO.userError "trusted theorem missing"
    unless candidate.type == expected.type do
      throw <| IO.userError "candidate theorem has the wrong type"
    unless candidate.isTheorem do
      throw <| IO.userError "candidate is not a theorem"
    let axioms := axiomClosure env [`patched_authorize_sound]
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    for ax in axioms do
      unless allowed.contains ax do
        throw <| IO.userError s!"unauthorized axiom: {ax}"
    IO.println s!"AUDITED_AXIOMS {axioms.toArray}"
    pure 0
