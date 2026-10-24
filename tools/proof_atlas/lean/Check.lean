import Lean
import Lean.Util.CollectAxioms

/-!
The proof-atlas trial command keeps incomplete candidates in the metavariable context.
It never fills a goal or declares an axiom. A complete candidate is checked by Lean's
kernel and its transitive axioms are reported before the result is accepted by Python.
This file is embedded in a temporary Lean source by `verify.py`; no build artifact is needed.
-/

open Lean Meta Elab Command

namespace ProofAtlasTrial

abbrev Aliases := Std.HashMap FVarId String

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields
private def str (s : String) : Json := toJson s

private def binderMode : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private partial def levelJson : Level → Json
  | .zero => obj [("kind", str "zero")]
  | .succ u => obj [("kind", str "succ"), ("of", levelJson u)]
  | .max u v => obj [("kind", str "max"), ("left", levelJson u), ("right", levelJson v)]
  | .imax u v => obj [("kind", str "imax"), ("left", levelJson u), ("right", levelJson v)]
  | .param n => obj [("kind", str "param"), ("name", str n.toString)]
  | .mvar n => obj [("kind", str "mvar"), ("id", str n.name.toString)]

/-- Exact expression sharing, without definitional equality or proof irrelevance. -/
private structure ExprDagState where
  seen : Std.HashMap ExprStructEq Nat := {}
  nodes : Array Json := #[]
  remaining : Nat := 0

private def refJson (id : Nat) : Json := obj [("kind", str "ref"), ("id", toJson id)]

private def addExprNode (e : Expr) (node : Json) : StateM ExprDagState Nat := do
  let id := (← get).nodes.size
  modify fun s => { s with nodes := s.nodes.push node, seen := s.seen.insert ⟨e⟩ id }
  return id

/-- Zero budget means unlimited; a finite budget counts unique complete nodes. -/
private partial def exprDagRef (aliases : Aliases) (limited : Bool) (e : Expr) :
    StateM ExprDagState Nat := do
  let key : ExprStructEq := ⟨e⟩
  if let some id := (← get).seen[key]? then return id
  if limited then
    if (← get).remaining == 0 then
      return ← addExprNode e (obj [("kind", str "truncated"),
        ("fingerprint", str (toString e.hash))])
    modify fun s => { s with remaining := s.remaining - 1 }
  let node : Json ← match e with
    | .bvar i => pure <| obj [("kind", str "bvar"), ("index", toJson i)]
    | .fvar i => pure <| obj [("kind", str "fvar"),
        ("id", str ((aliases[i]?).getD i.name.toString))]
    | .mvar i => pure <| obj [("kind", str "mvar"), ("id", str i.name.toString)]
    | .sort u => pure <| obj [("kind", str "sort"), ("level", levelJson u)]
    | .const n us => pure <| obj [("kind", str "const"), ("name", str n.toString),
        ("levels", toJson (us.map levelJson))]
    | .app f a => pure <| obj [("kind", str "app"),
        ("fn", refJson (← exprDagRef aliases limited f)),
        ("arg", refJson (← exprDagRef aliases limited a))]
    | .lam n t b bi => pure <| obj [("kind", str "lam"),
        ("binder_name", str n.toString), ("binder_info", str (binderMode bi)),
        ("type", refJson (← exprDagRef aliases limited t)),
        ("body", refJson (← exprDagRef aliases limited b))]
    | .forallE n t b bi => pure <| obj [("kind", str "forallE"),
        ("binder_name", str n.toString), ("binder_info", str (binderMode bi)),
        ("type", refJson (← exprDagRef aliases limited t)),
        ("body", refJson (← exprDagRef aliases limited b))]
    | .letE n t v b nondep => pure <| obj [("kind", str "letE"),
        ("binder_name", str n.toString), ("type", refJson (← exprDagRef aliases limited t)),
        ("value", refJson (← exprDagRef aliases limited v)),
        ("body", refJson (← exprDagRef aliases limited b)), ("nondep", toJson nondep)]
    | .lit (.natVal n) => pure <| obj [("kind", str "lit"),
        ("literal_kind", str "nat"), ("value", toJson n)]
    | .lit (.strVal s) => pure <| obj [("kind", str "lit"),
        ("literal_kind", str "string"), ("value", str s)]
    | .mdata _ e => pure <| obj [("kind", str "mdata"),
        ("expr", refJson (← exprDagRef aliases limited e))]
    | .proj n i e => pure <| obj [("kind", str "proj"), ("type_name", str n.toString),
        ("index", toJson i), ("struct", refJson (← exprDagRef aliases limited e))]
  addExprNode e node

private def exprJson (aliases : Aliases) (e : Expr) (budget : Nat := 0) : Json :=
  let (root, state) := (exprDagRef aliases (budget != 0) e).run { remaining := budget }
  obj [("kind", str "dag"), ("root", toJson root), ("nodes", Json.arr state.nodes)]

private def deps (aliases : Aliases) (e : Expr) : Array String :=
  (collectFVars {} e).fvarIds.filterMap (fun id => aliases[id]?)

private def pp (e : Expr) : MetaM String := return (← ppExpr e).pretty

private def localRecord (aliases : Aliases) (id : String) (index : Nat)
    (d : LocalDecl) (budget : Nat) : MetaM Json := do
  let t ← instantiateMVars d.type
  let value ← d.value?.mapM instantiateMVars
  return obj [
    ("id", str id), ("fvar_id", str d.fvarId.name.toString),
    ("index", toJson index), ("name", str d.userName.toString),
    ("binder_mode", str (binderMode d.binderInfo)),
    ("role", str (if ← isProp t then "condition" else "object")),
    ("type_text", str (← pp t)), ("type_expr", exprJson aliases t budget),
    ("depends_on", toJson (deps aliases t)), ("is_let", toJson value.isSome),
    ("value_text", toJson (← value.mapM pp)),
    ("value_expr", (value.map (fun e => exprJson aliases e budget)).getD Json.null)]


private def emit (token : String) (status : String) (goals : Array String)
    (goalTypes : Array String) (kernelChecked : Bool) (axioms : Array String)
    (target : String) (error : String := "") : TermElabM Unit := do
  let result := Json.mkObj [
    ("status", toJson status),
    ("remaining_goals", toJson goals),
    ("remaining_goal_types", toJson goalTypes),
    ("kernel_checked", toJson kernelChecked),
    ("axioms", toJson axioms),
    ("target", toJson target),
    ("error", toJson error)]
  IO.println s!"PROOF_ATLAS_JSON[{token}] {result.compress}"

private def unsolved (root : Expr) (reported : List MVarId := []) :
    MetaM (Array MVarId) := do
  let mut result : Array MVarId := #[]
  for g in reported.toArray ++ (← getMVars root) do
    unless (← g.isAssigned) || result.contains g do
      result := result.push g
  return result

private def describe (goals : Array MVarId) : MetaM (Array String × Array String) := do
  let mut states : Array String := #[]
  let mut types : Array String := #[]
  for g in goals do
    states := states.push (← ppGoal g).pretty
    types := types.push (← g.withContext do ppExpr (← g.getType)).pretty
  return (states, types)

private def expressionAxioms (expressions : Array Expr) : MetaM (Array Name) := do
  let mut constants : Array Name := #[]
  for expression in expressions do
    constants := constants ++ expression.getUsedConstants
  for declaration in ← getLCtx do
    constants := constants ++ declaration.type.getUsedConstants
    if let some value := declaration.value? then
      constants := constants ++ value.getUsedConstants
  let mut result : Array Name := #[]
  for constant in constants do
    for axiomName in ← collectAxioms constant do
      unless result.contains axiomName do
        result := result.push axiomName
  return result

syntax (name := proofAtlasState) "#proof_atlas_state " str num " : " term : command

elab_rules : command
  | `(#proof_atlas_state $token:str $budget:num : $target:term) =>
    runTermElabM fun parameters => do
      let target ← Term.elabType target
      Term.synthesizeSyntheticMVarsNoPostponing
      let target ← instantiateMVars target
      let closedType ← mkForallFVars parameters target
      let closedType ← Term.levelMVarToParam (← instantiateMVars closedType)
      checkWithKernel closedType
      let mut aliases : Aliases := {}
      for h : i in [:parameters.size] do
        aliases := aliases.insert parameters[i].fvarId! s!"b{i}"
      let mut binders : Array Json := #[]
      for h : i in [:parameters.size] do
        binders := binders.push (← localRecord aliases s!"b{i}" i
          (← parameters[i].fvarId!.getDecl) budget.getNat)
      let target ← instantiateMVars target
      let result := obj [
        ("status", str "elaborated"),
        ("state_elaborated", toJson true),
        ("kernel_checked", toJson false),
        ("type_kernel_checked", toJson true),
        ("ordered_telescope", Json.arr binders),
        ("target_text", str (← pp target)),
        ("target_expr", exprJson aliases target budget.getNat),
        ("type_expr", exprJson {} closedType budget.getNat),
        ("universe_params", toJson ((collectLevelParams {} closedType).params.map toString)),
        ("expr_budget", toJson budget.getNat)]
      IO.println s!"PROOF_ATLAS_STATE[{token.getString}] {result.compress}"

syntax (name := proofAtlasObject) "#proof_atlas_object " str str " := " term : command

elab_rules : command
  | `(#proof_atlas_object $token:str $role:str := $expression:term) =>
    runTermElabM fun parameters => do
      let value ← Term.elabTerm expression none
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      unless (← getMVars value).isEmpty do
        throwError "object mapping expression contains unresolved metavariables"
      let closed ← mkLambdaFVars parameters value
      let closed ← Term.levelMVarToParam (← instantiateMVars closed)
      checkWithKernel closed
      let type ← inferType value
      let result := Json.mkObj [
        ("role", toJson role.getString),
        ("elaborated_expression", toJson (← ppExpr value).pretty),
        ("inferred_type", toJson (← ppExpr type).pretty),
        ("kernel_checked", toJson true),
        ("axioms", toJson ((← expressionAxioms #[value, type]).map toString))]
      IO.println s!"PROOF_ATLAS_OBJECT[{token.getString}] {result.compress}"

syntax (name := proofAtlasCheck) "#proof_atlas_check " str " : " term " := " "by " tacticSeq :
  command

elab_rules : command
  | `(#proof_atlas_check $token:str : $target:term := by $tactics:tacticSeq) =>
    runTermElabM fun parameters => do
      let expected ← Term.elabType target
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let expectedText := (← ppExpr expected).pretty
      let root ← mkFreshExprMVar expected
      try
        let goals ← Tactic.run root.mvarId! (Tactic.evalTactic tactics)
        let proof ← instantiateMVars root
        let remaining ← unsolved proof goals
        if !remaining.isEmpty then
          let (states, types) ← describe remaining
          emit token.getString "partial" states types false #[] expectedText
        else
          Term.synthesizeSyntheticMVarsNoPostponing
          let proof ← instantiateMVars proof
          let remaining ← unsolved proof
          if !remaining.isEmpty then
            let (states, types) ← describe remaining
            emit token.getString "partial" states types false #[] expectedText
          else
            if proof.hasSorry then
              throwError "candidate contains an unproved placeholder"
            unless ← isDefEq (← inferType proof) expected do
              throwError "candidate proof does not have the requested goal type"
            let closed ← mkLambdaFVars parameters proof
            let closed ← Term.levelMVarToParam (← instantiateMVars closed)
            checkWithKernel closed
            let axioms ← expressionAxioms #[closed, expected]
            emit token.getString "complete" #[] #[] true
              (axioms.map toString) expectedText
      catch ex =>
        let (states, types) ← describe (← unsolved root)
        emit token.getString "rejected" states types false #[] expectedText
          (← ex.toMessageData.toString)

end ProofAtlasTrial
