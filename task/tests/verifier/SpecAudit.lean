import SecurityChallenge
import Lean

open Lean Meta SecurityChallenge

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
        let axioms := if ci.isAxiom || ci.isUnsafe then axioms.insert name else axioms
        axiomClosure env (deps ++ rest) seen axioms

def audit (env : Environment) (name : Name) (expected : Expr) (theoremOnly := false) : MetaM Unit := do
  let some ci := env.find? name | throwError "missing declaration {name}"
  unless ← isDefEq ci.type expected do throwError "wrong type for {name}"
  if theoremOnly && !ci.isTheorem then throwError "expected theorem {name}"
  for ax in (axiomClosure env [name]).toArray do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unauthorized axiom or unsafe dependency: {ax}"

def node (op : String) (args : Array Json := #[]) : Json :=
  Json.mkObj [("op", toJson op), ("args", Json.arr args)]

-- Serialize kernel Exprs, never candidate text. Unknown heads are unfolded
-- only when definitional reduction makes progress, with a finite fuel budget.
partial def lower (e : Expr) (vars : Array Expr) (fuel : Nat := 512) : MetaM Json := do
  if fuel == 0 then throwError "unsupported: normalization/expression budget"
  let e := e.consumeMData.headBeta
  let fn := e.getAppFn
  let args := e.getAppArgs
  let recur := fun x => lower x vars (fuel-1)
  let name := fn.constName?
  if name == some ``UInt64.toNat && args.size == 1 then
    let input ← withTransparency .all (whnf args[0]!)
    if let some i := vars.findIdx? (· == input) then
      return Json.mkObj [("var", toJson i)]
    let reduced ← whnf e
    if let .lit (.natVal n) := reduced then return Json.mkObj [("nat", toJson n)]
    throwError "unsupported: UInt64.toNat on a non-input expression"
  if let .lit (.natVal n) := e then return Json.mkObj [("nat", toJson n)]
  if name == some ``True then return node "true"
  if name == some ``False then return node "false"
  if name == some ``Nat.add && args.size == 2 then return node "add" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.sub && args.size == 2 then return node "sub" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.mul && args.size == 2 then return node "mul" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.div && args.size == 2 then return node "div" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.mod && args.size == 2 then return node "mod" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.le && args.size == 2 then return node "le" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Nat.lt && args.size == 2 then return node "lt" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Eq && args.size == 3 then
    let typ ← whnf args[0]!
    unless typ == mkConst ``Nat || typ == mkSort .zero do
      throwError "unsupported: equality outside Nat/Prop"
    return node "eq" #[← recur args[1]!, ← recur args[2]!]
  if name == some ``And && args.size == 2 then return node "and" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Or && args.size == 2 then return node "or" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Iff && args.size == 2 then return node "iff" #[← recur args[0]!, ← recur args[1]!]
  if name == some ``Not && args.size == 1 then return node "not" #[← recur args[0]!]
  if name == some ``ite && args.size == 5 then
    return node "if" #[← recur args[1]!, ← recur args[3]!, ← recur args[4]!]
  if e.isForall then
    let .forallE _ dom body _ := e | unreachable!
    unless ← isProp dom do throwError "unsupported: quantified binders"
    if body.hasLooseBVars then throwError "unsupported: dependent implication"
    return node "implies" #[← recur dom, ← recur body]
  -- Reduce one layer only. A wholesale whnf would unfold a newly exposed
  -- if into Decidable.rec and lose the supported conditional's head.
  if let .letE _ _ value body _ := fn then
    return ← recur (mkAppN (body.instantiate1 value) args)
  if let some projected ← reduceProj? fn then
    return ← recur (mkAppN projected args)
  if let .const n levels := fn then
    if let some (.defnInfo info) := (← getEnv).find? n then
      return ← recur (mkAppN (info.value.instantiateLevelParams info.levelParams levels) args)
  if !e.hasFVar then
    let reduced ← whnf e
    if reduced != e then return ← recur reduced
  throwError "unsupported expression head: {fn}"

def exportSpec : MetaM Json := do
  withLocalDeclD `balance (mkConst ``UInt64) fun b =>
    withLocalDeclD `amount (mkConst ``UInt64) fun a =>
      withLocalDeclD `fee (mkConst ``UInt64) fun f =>
        withLocalDeclD `total (mkConst ``UInt64) fun t => do
          let candidate := mkConst `candidateSpec
          let accepts ← mkAppM ``AuthorizationSpec.accepts #[candidate, b, a, f]
          let output ← mkAppM ``AuthorizationSpec.output #[candidate, b, a, f, t]
          let av ← try lower accepts #[b,a,f,t]
                   catch err => pure <| Json.mkObj [("unsupported", toJson (← err.toMessageData.toString))]
          let ov ← try lower output #[b,a,f,t]
                   catch err => pure <| Json.mkObj [("unsupported", toJson (← err.toMessageData.toString))]
          return Json.mkObj [("accepts",av),("output",ov)]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mode := args.headD "spec"
  let modules := if mode == "proof" then #[`CandidateSpec, `CandidateAudit, `CandidateProof]
                 else if mode == "verdict" then #[`CandidateAudit]
                 else #[`CandidateSpec]
  withImportModules (modules.map fun m => {module := m}) {} fun env => do
    let (result, _) ← (do
      if mode != "verdict" then audit env `candidateSpec (mkConst ``AuthorizationSpec)
      if mode == "spec" then
        try return ← exportSpec
        catch err => return Json.mkObj [("unsupported", toJson (← err.toMessageData.toString))]
      audit env `verdict (mkConst ``AuditVerdict)
      let v ← withTransparency .all (whnf (mkConst `verdict))
      unless v == mkConst ``AuditVerdict.safe || v == mkConst ``AuditVerdict.vulnerable do
        throwError "verdict must reduce to safe or vulnerable"
      if mode == "proof" then
        let expected ← mkAppM ``AuditClaim #[mkConst `candidateSpec, mkConst `verdict]
        audit env `auditEvidence expected true
      return Json.mkObj [("verdict", toJson (if v == mkConst ``AuditVerdict.safe then "safe" else "vulnerable")),
                         ("audit", toJson "kernel replay, type and transitive axioms")]
      : MetaM Json).toIO {fileName := "trusted-audit", fileMap := default} {env := env}
    IO.println result.compress
    pure 0
