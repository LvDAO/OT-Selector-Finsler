import Lean

/-!
Standalone extraction of compiled declaration dependencies, proof abstraction
triads and source tactic states. Run with `lake env lean --run` from the project
root. This tool does not add declarations to the mathematical library.
-/

open Lean Meta Elab

namespace ProofAtlas

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

private def exprJson (aliases : Aliases) (e : Expr) (budget : Nat := 0) : Json := Id.run do
  let (root, state) := (exprDagRef aliases (budget != 0) e).run { remaining := budget }
  let complete := !state.nodes.any (fun n => (n.getObjValAs? String "kind").toOption == some "truncated")
  return obj [("kind", str "dag"), ("root", toJson root), ("nodes", Json.arr state.nodes),
    ("complete", toJson complete), ("budget", toJson budget)]

private def constKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some i => some env.header.modules[i.toNat]!.module
  | none => if env.contains n then some env.mainModule else none

private def sourceRange (r : DeclarationRange) : Json := obj [
  ("start", toJson r.pos), ("end", toJson r.endPos),
  ("start_utf16_column", toJson r.charUtf16), ("end_utf16_column", toJson r.endCharUtf16)]

private def deps (aliases : Aliases) (e : Expr) : Array String :=
  (collectFVars {} e).fvarIds.filterMap (fun id => aliases[id]?)

private def pp (e : Expr) : MetaM String := do
  let start ← IO.getNumHeartbeats
  try
    withTheReader Core.Context (fun c => { c with
      initHeartbeats := start, maxHeartbeats := 1000000 }) do
      withOptions (fun o => (o.set `pp.maxSteps (500 : Nat)).set `pp.deepTerms.threshold (30 : Nat)) do
        return (← ppExpr e).pretty
  catch _ =>
    return "[pretty_print_unavailable: rendering budget exceeded; exact expression retained]"

private def proofBudgeted (act : MetaM α) : MetaM α := do
  let start ← IO.getNumHeartbeats
  withTheReader Core.Context (fun c => { c with
    initHeartbeats := start, maxHeartbeats := 200000000 }) act

/-- Bounded syntactic rendering; never infers types or unfolds compiled terms. -/
private partial def syntaxTextAux (aliases : Aliases) (depth : Nat) (e : Expr) : StateM Nat String := do
  if depth == 0 || (← get) == 0 then return "⋯[syntax budget]"
  modify (· - 1)
  let child := syntaxTextAux aliases (depth - 1)
  match e with
  | .bvar i => return s!"#{i}"
  | .fvar i => return (aliases[i]?).getD i.name.toString
  | .mvar i => return s!"?{i.name}"
  | .sort u => return s!"Sort({u})"
  | .const n _ => return n.toString
  | .app f a => return s!"({← child f} {← child a})"
  | .lam n t b _ => return s!"(fun {n} : {← child t} => {← child b})"
  | .forallE n t b _ => return s!"(∀ {n} : {← child t}, {← child b})"
  | .letE n t v b _ => return s!"(let {n} : {← child t} := {← child v}; {← child b})"
  | .lit (.natVal n) => return toString n
  | .lit (.strVal v) => return (toJson v).compress
  | .mdata _ b => child b
  | .proj n i b => return s!"({← child b}).{n}.{i}"

private def syntaxText (aliases : Aliases) (e : Expr) : String :=
  (syntaxTextAux aliases 40 e).run' 1000

private def localRecord (aliases : Aliases) (id : String) (index : Nat)
    (d : LocalDecl) : MetaM Json := do
  let t ← instantiateMVars d.type
  let value ← d.value?.mapM instantiateMVars
  return obj [
    ("id", str id), ("fvar_id", str d.fvarId.name.toString),
    ("index", toJson index), ("name", str d.userName.toString),
    ("binder_mode", str (binderMode d.binderInfo)),
    ("role", str (if ← isProp t then "condition" else "object")),
    ("type_text", str (syntaxText aliases t)), ("type_text_status", str "bounded_syntax"),
    ("type_expr", exprJson aliases t),
    ("depends_on", toJson (deps aliases t)), ("is_let", toJson value.isSome),
    ("value_text", toJson (value.map (syntaxText aliases))),
    ("value_expr", (value.map (fun e => exprJson aliases e 2000)).getD Json.null)]

private def headName (aliases : Aliases) (e : Expr) : String :=
  let f := e.getAppFn
  if f.isConst then f.constName!.toString
  else if f.isFVar then (aliases[f.fvarId!]?).getD f.fvarId!.name.toString
  else if f.isMVar then f.mvarId!.name.toString
  else "<expression>"

private partial def syntacticBodyHead (e : Expr) : String :=
  match e with
  | .lam _ _ b _ | .letE _ _ _ b _ | .mdata _ b => syntacticBodyHead b
  | _ => headName {} e

private def proofSkeleton (aliases : Aliases) (e target : Expr) (budget : Nat) : MetaM Json := do
  let mut args := #[]
  let mut functionType : Option Expr := none
  if !e.getAppArgs.isEmpty then
    let .const name levels := e.getAppFn | throwError "Application head is not a syntactic constant; no normalization performed"
    let ci ← getConstInfo name
    functionType := some (ci.type.instantiateLevelParams ci.levelParams levels)
  for h : i in [:e.getAppArgs.size] do
    let a := e.getAppArgs[i]
    let some ft := functionType | throwError "Missing application function type"
    let .forallE _ t body _ := ft | throwError "Application domain requires normalization; no normalization performed"
    let proofArg ← isProp t
    let text := if proofArg then headName aliases a else syntaxText aliases a
    args := args.push (obj [
      ("index", toJson i), ("expression_text", str text),
      ("expression_text_status", str (if proofArg then "head_only" else "bounded_syntax")),
      ("expr", exprJson aliases a budget), ("type_text", str (syntaxText aliases t)),
      ("type_expr", exprJson aliases t budget), ("type_origin", str "application_domain"),
      ("is_proof", toJson proofArg), ("depends_on", toJson (deps aliases a)),
      ("constants", toJson (a.getUsedConstants.map Name.toString))])
    functionType := some (body.instantiate1 a)
  return obj [
    ("status", str "available"), ("scope", str "closed_declaration"),
    ("head", str (headName aliases e)),
    ("syntactic_body_head", str (syntacticBodyHead e)),
    ("expression_text", str (headName aliases e)), ("expression_text_status", str "head_only"),
    ("expr", exprJson aliases e budget), ("type_expr", exprJson aliases target),
    ("type_origin", str "compiled_declaration_target"),
    ("arguments", Json.arr args), ("fingerprint", str (toString e.hash)),
    ("fingerprint_kind", str "lean_expr_hash_bucket_only"), ("expr_budget", toJson budget),
    ("constants", toJson (e.getUsedConstants.map Name.toString))]

private def triad (ci : ConstantInfo) (proofBudget : Nat) : MetaM Json :=
  forallTelescope ci.type fun xs target => do
    IO.eprintln s!"proof-atlas stage=triad_context name={ci.name}"
    let mut aliases : Aliases := {}
    for h : i in [:xs.size] do
      aliases := aliases.insert xs[i].fvarId! s!"b{i}"
    let mut binders := #[]
    for h : i in [:xs.size] do
      binders := binders.push (← localRecord aliases s!"b{i}" i (← xs[i].fvarId!.getDecl))
    let body := ci.value? (allowOpaque := true)
    IO.eprintln s!"proof-atlas stage=proof_skeleton name={ci.name}"
    let skeleton ← body.mapM fun e => do
      try proofBudgeted (proofSkeleton {} e ci.type proofBudget)
      catch ex => return obj [("status", str "unavailable"),
        ("reason", str (← ex.toMessageData.toString)),
        ("type_expr", exprJson aliases target), ("type_origin", str "compiled_declaration_target")]
    let detailStatus := if skeleton.isSome then
      ((skeleton.get!).getObjValAs? String "status").toOption.getD "unavailable" else "no_body"
    IO.eprintln s!"proof-atlas stage=triad_done name={ci.name} detail={detailStatus}"
    return obj [
      ("record_type", str "triad"), ("declaration", str ci.name.toString),
      ("universe_params", toJson (ci.levelParams.map Name.toString)),
      ("ordered_telescope", Json.arr binders),
      ("target_text", str (syntaxText aliases target)),
      ("target_text_status", str "bounded_syntax"),
      ("target_expr", exprJson aliases target), ("type_expr", exprJson {} ci.type),
      ("proof_skeleton", skeleton.getD Json.null), ("proof_detail_status", str detailStatus)]

private def goalRecord (g : MVarId) : MetaM Json := do
  let d ← g.getDecl
  withLCtx d.lctx d.localInstances do
    let mut aliases : Aliases := {}
    let mut locals := #[]
    for l in d.lctx do
      let id := s!"h{locals.size}"
      aliases := aliases.insert l.fvarId id
      locals := locals.push l
    let mut hypotheses := #[]
    for h : i in [:locals.size] do
      hypotheses := hypotheses.push (← localRecord aliases s!"h{i}" i locals[i])
    let target ← instantiateMVars d.type
    return obj [
      ("id", str g.name.toString), ("scope", str g.name.toString),
      ("target_text", str (syntaxText aliases target)),
      ("target_text_status", str "bounded_syntax"),
      ("target_expr", exprJson aliases target), ("hypotheses", Json.arr hypotheses)]

private def jsonTextField (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

private def goalRecordsText (goals : List Json) : String :=
  String.intercalate "\n\n" (goals.map fun g =>
    let hypotheses := ((g.getObjValAs? (Array Json) "hypotheses").toOption.getD #[]).toList
    let lines := hypotheses.map fun h => s!"{jsonTextField h "id"} ({jsonTextField h "name"}) : {jsonTextField h "type_text"}"
    String.intercalate "\n" (lines ++ [s!"⊢ {jsonTextField g "target_text"}"]))

private def assignmentRecord (g : MVarId) (budget : Nat) : MetaM Json := do
  let assignment ← getExprMVarAssignment? g
  let some e := assignment | return obj [("goal_id", str g.name.toString),
    ("assigned", toJson false)]
  let d ← g.getDecl
  withLCtx d.lctx d.localInstances do
    let mut aliases : Aliases := {}
    let mut index : Nat := 0
    for l in d.lctx do
      aliases := aliases.insert l.fvarId s!"h{index}"
      index := index + 1
    return obj [("goal_id", str g.name.toString), ("assigned", toJson true),
      ("assignment_text", str (headName aliases e)), ("assignment_text_status", str "head_only"),
      ("assignment_expr", exprJson aliases e budget),
      ("referenced_goal_ids", toJson ((e.collectMVars {}).result.map (fun m => m.name.toString)))]

private def options : Options :=
  Lean.maxRecDepth.set (Lean.maxHeartbeats.set {} 0) 10000

private def runMeta (env : Environment) (act : MetaM α) : IO α :=
  ({ env, opts := options } : PPContext).runMetaM act

structure Args where
  command : String
  values : Array (String × String) := #[]

private def Args.all (a : Args) (key : String) : Array String :=
  a.values.filterMap (fun (k, v) => if k == key then some v else none)

private def Args.get (a : Args) (key : String) (fallback : String := "") : String :=
  (a.all key).back?.getD fallback

private def help : String :=
  "Usage: lake env lean --run tools/proof_atlas/lean/ProofAtlas.lean COMMAND OPTIONS\n" ++
  "  export --module MOD --output PATH [--triads public|all|none]\n" ++
  "         [--project-prefix OTSelector --project-prefix LeanPool ...]\n" ++
  "  detail --module MOD --name DECL --output PATH\n" ++
  "  trace --file FILE --output PATH [--name DECL] [--module SOURCE_MODULE]\n" ++
  "  Optional: --proof-budget N (default 2000; 0 means unlimited), --limit N.\n" ++
  "  Export partitions: --shard-count N --shard-index I (zero-based I < N).\n" ++
  "  Repeated --module imports are supported for export/detail."

private def parseArgs (args : List String) : Except String Args := do
  let command :: rest := args | throw help
  if !["export", "detail", "trace"].contains command then throw help
  let rec go (xs : List String) (acc : Array (String × String)) : Except String Args := do
    match xs with
    | [] => return { command, values := acc }
    | key :: value :: tail =>
      if !["--module", "--output", "--name", "--file", "--triads", "--project-prefix",
          "--proof-budget", "--limit", "--shard-count", "--shard-index"].contains key then
        throw s!"Unknown option: {key}\n{help}"
      if value.startsWith "--" then throw s!"Missing value for {key}"
      go tail (acc.push (key, value))
    | [key] => throw s!"Missing value for {key}"
  let a ← go rest #[]
  if a.get "--output" == "" then throw "--output is required"
  if command == "trace" && a.get "--file" == "" then throw "trace requires --file"
  if command == "detail" && a.get "--name" == "" then throw "detail requires --name"
  if !["public", "all", "none"].contains (a.get "--triads" "public") then
    throw "--triads must be public, all, or none"
  for key in ["--limit", "--proof-budget", "--shard-count", "--shard-index"] do
    if a.get key != "" && (a.get key).toNat?.isNone then throw s!"{key} needs a natural number"
  let shardCount := (a.get "--shard-count" "1").toNat!
  let shardIndex := (a.get "--shard-index" "0").toNat!
  if shardCount == 0 then throw "--shard-count must be positive"
  if shardIndex >= shardCount then throw "--shard-index must be smaller than --shard-count"
  if command != "export" && (shardCount != 1 || shardIndex != 0) then
    throw "Sharding applies only to export"
  return a

private def exportScope (a : Args) : String :=
  if a.command == "detail" then "named_declaration"
  else if (a.get "--shard-count" "1").toNat! > 1 then "hash_shard"
  else if (a.get "--limit" "0").toNat! > 0 then "limited_selection"
  else if a.command == "export" &&
      ((a.all "--module").isEmpty || a.all "--module" == #["OTSelector"]) &&
      (a.all "--project-prefix").isEmpty then "full_project"
  else "module_selection"

private def emit (out : IO.FS.Handle) (j : Json) : IO Unit := do
  out.putStrLn j.compress
  out.flush

private def manifest (a : Args) (env : Environment) : Json := obj [
  ("record_type", str "manifest"), ("schema_version", toJson (1 : Nat)),
  ("ast_encoding", str "expr_dag_v1"),
  ("lean_version", str Lean.versionString), ("command", str a.command),
  ("shard_count", toJson ((a.get "--shard-count" "1").toNat!)),
  ("shard_index", toJson ((a.get "--shard-index" "0").toNat!)),
  ("partition_rule", str "Lean.Name.hash.toNat % shard_count"),
  ("export_scope", str (exportScope a)),
  ("imports", toJson (env.header.modules.map (fun m => m.module.toString))),
  ("arguments", toJson a.values), ("proof_budget", toJson ((a.get "--proof-budget" "2000").toNat!)),
  ("proof_detail_heartbeats", toJson (200000 : Nat)),
  ("text_rendering", obj [("max_steps", toJson (500 : Nat)),
    ("depth_threshold", toJson (30 : Nat)), ("heartbeats", toJson (1000 : Nat)),
    ("may_elide", toJson true), ("unavailable_marker", str "[pretty_print_unavailable:")])]

private def declaration (env : Environment) (ci : ConstantInfo) : MetaM Json := do
  let ranges ← findDeclarationRanges? ci.name
  let doc ← findDocString? env ci.name
  return obj [
    ("record_type", str "declaration"), ("name", str ci.name.toString),
    ("module", toJson ((moduleOf env ci.name).map Name.toString)),
    ("kind", str (constKind ci)), ("external", toJson false),
    ("private", toJson (isPrivateName ci.name)),
    ("internal_detail", toJson ci.name.isInternalDetail),
    ("aux_recursor", toJson (isAuxRecursor env ci.name)),
    ("no_confusion", toJson (isNoConfusion env ci.name)),
    ("user_name", str ((privateToUserName? ci.name).getD ci.name).toString),
    ("mutual_group", toJson (ci.all.map Name.toString)),
    ("type_dependencies", toJson (ci.type.getUsedConstants.map Name.toString)),
    ("proof_dependencies", toJson (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants)
      |>.getD #[] |>.map Name.toString)),
    ("body_present", toJson (ci.value? (allowOpaque := true)).isSome),
    ("type_text", str (← pp ci.type)), ("docstring", toJson doc),
    ("range", (ranges.map (sourceRange ·.range)).getD Json.null),
    ("selection_range", (ranges.map (sourceRange ·.selectionRange)).getD Json.null)]

private def exportEnv (a : Args) (env : Environment) (out : IO.FS.Handle) : IO UInt32 := do
  emit out (manifest a env)
  let proofBudget := (a.get "--proof-budget" "2000").toNat!
  let limit := (a.get "--limit" "0").toNat!
  let wanted := a.get "--name"
  let shardCount := (a.get "--shard-count" "1").toNat!
  let shardIndex := (a.get "--shard-index" "0").toNat!
  -- Resolve the immutable module-selection predicate once for this export.
  let requestedPrefixes := a.all "--project-prefix"
  let prefixes := (if requestedPrefixes.isEmpty then
    #["OTSelector", "LeanPool", "LeanLevy"] else requestedPrefixes).map (fun p => p.toName)
  let eligibleModule := fun n => prefixes.any (fun p => p.isPrefixOf n)
  let eligibleModules := env.header.modules.map (fun m => eligibleModule m.module)
  let eligibleMainModule := eligibleModule env.mainModule
  let mut refs : NameSet := {}
  let mut count : Nat := 0
  let mut triads : Nat := 0
  let mut failures : Nat := 0
  let mut unavailable : Nat := 0
  let (names, projectOwnedCount) : Array Name × Nat :=
    if a.command == "detail" then (#[wanted.toName], 1) else Id.run do
      let mut result : Array Name := #[]
      let mut total : Nat := 0
      for (name, idx) in env.const2ModIdx do
        if eligibleModules[idx.toNat]! && (env.find? name).isSome then
          total := total + 1
          if name.hash.toNat % shardCount == shardIndex then
            result := result.push name
      return (result, total)
  for name in names do
    let some ci := env.find? name | continue
    if limit != 0 && count >= limit then break
    count := count + 1
    try
      IO.eprintln s!"proof-atlas stage=declaration name={ci.name}"
      emit out (← runMeta env (declaration env ci))
      for d in ci.type.getUsedConstants ++
          (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]) do
        refs := refs.insert d
      let includeTriad := a.command == "detail" ||
        (ci.isTheorem && (a.get "--triads" "public" == "all" ||
          (a.get "--triads" "public" == "public" &&
            !isPrivateName ci.name && !ci.name.isInternalDetail)))
      if includeTriad then
        let t ← runMeta env (triad ci proofBudget)
        if (t.getObjValAs? String "proof_detail_status").toOption == some "unavailable" then
          unavailable := unavailable + 1
        emit out t
        triads := triads + 1
    catch e =>
      failures := failures + 1
      emit out (obj [("record_type", str "diagnostic"), ("severity", str "error"),
        ("declaration", str ci.name.toString), ("message", str (toString e))])
  if count == 0 then
    failures := failures + 1
    emit out (obj [("record_type", str "diagnostic"), ("severity", str "error"),
      ("message", str "No matching declarations in imported environment")])
  let mut externalCount : Nat := 0
  for n in refs do
    let isEligible := match env.getModuleIdxFor? n with
      | some idx => eligibleModules[idx.toNat]!
      | none => env.contains n && eligibleMainModule
    if isEligible then continue
    externalCount := externalCount + 1
    emit out (obj [("record_type", str "declaration"), ("name", str n.toString),
      ("module", toJson ((moduleOf env n).map Name.toString)), ("external", toJson true),
      ("kind", toJson ((env.find? n).map constKind)), ("private", toJson (isPrivateName n)),
      ("internal_detail", toJson n.isInternalDetail)])
  emit out (obj [("record_type", str "summary"), ("declarations", toJson count),
    ("external_references", toJson externalCount), ("triads", toJson triads),
    ("proof_detail_unavailable", toJson unavailable),
    ("failures", toJson failures), ("complete", toJson (failures == 0 && limit == 0)),
    ("scope_complete", toJson (failures == 0 && limit == 0)),
    ("full_corpus", toJson (exportScope a == "full_project")),
    ("owned_count", toJson count), ("project_owned_count", toJson projectOwnedCount),
    ("export_scope", str (exportScope a)),
    ("shard_count", toJson shardCount), ("shard_index", toJson shardIndex)])
  return if failures == 0 then 0 else 1

private def traceSource (a : Args) (out : IO.FS.Handle) : IO UInt32 := do
  let file := a.get "--file"
  let source ← IO.FS.readFile file
  let input := Parser.mkInputContext source file
  let (header, parserState, msgs) ← Parser.parseHeader input
  let mainModule := (a.get "--module" "ProofAtlas.SourceTrace").toName
  let (env, msgs) ← processHeader header options msgs input (mainModule := mainModule)
  emit out (manifest a env)
  let state ← IO.processCommands input parserState (Command.mkState env msgs options)
  for msg in state.commandState.messages.toList do
    emit out (obj [("record_type", str "diagnostic"),
      ("severity", str (toString msg.severity)), ("message", str (← msg.toString))])
  if state.commandState.messages.hasErrors then
    emit out (obj [("record_type", str "summary"), ("complete", toJson false),
      ("replay_success", toJson false), ("fragments", toJson (0 : Nat))])
    return 1
  let mut found : Nat := 0
  let proofBudget := (a.get "--proof-budget" "2000").toNat!
  for (name, ci) in state.commandState.env.constants do
    if state.commandState.env.isImportedConst name then continue
    if !ci.isTheorem then continue
    if a.get "--name" != "" && name.toString != a.get "--name" then continue
    if a.get "--name" == "" && (name.isInternalDetail || isPrivateName name) then continue
    emit out (← runMeta state.commandState.env (declaration state.commandState.env ci))
    emit out (← runMeta state.commandState.env (triad ci proofBudget))
    found := found + 1
  if a.get "--name" != "" && found == 0 then
    emit out (obj [("record_type", str "diagnostic"), ("severity", str "error"),
      ("message", str "Named theorem was not declared by this source file")])
    return 1
  let count ← IO.mkRef (0 : Nat)
  for tree in state.commandState.infoState.trees do
    tree.visitM' (postNode := fun ctx info _ => do
      let some parent := ctx.parentDecl? | return
      if a.get "--name" != "" && parent.toString != a.get "--name" then return
      let .ofTacticInfo ti := info | return
      let beforeCtx := { ctx with mctx := ti.mctxBefore }
      let afterCtx := { ctx with mctx := ti.mctxAfter }
      let before ← beforeCtx.runMetaM {} (ti.goalsBefore.mapM goalRecord)
      let after ← afterCtx.runMetaM {} (ti.goalsAfter.mapM goalRecord)
      let assignments ← afterCtx.runMetaM {} (ti.goalsBefore.mapM (assignmentRecord · proofBudget))
      let beforeText := goalRecordsText before
      let afterText := goalRecordsText after
      let index ← count.get
      emit out (obj [
        ("record_type", str "proof_fragment"), ("id", str s!"fragment{index}"),
        ("declaration", str parent.toString), ("file", str file),
        ("source", str ((ti.stx.getSubstring? false false).map (·.toString) |>.getD (ti.stx.reprint.getD ""))),
        ("source_original", toJson ((ti.stx.getSubstring? false false).map (·.toString))),
        ("syntax_reprint", str (ti.stx.reprint.getD "")),
        ("source_kind", str (match ti.stx.getHeadInfo with
          | .original .. => "original" | .synthetic .. => "synthetic" | .none => "none")),
        ("syntax_kind", str ti.stx.getKind.toString),
        ("start", toJson (ti.stx.getPos?.map input.fileMap.toPosition)),
        ("end", toJson (ti.stx.getTailPos?.map input.fileMap.toPosition)),
        ("goals_before", toJson before), ("goals_after", toJson after),
        ("goals_before_text", str beforeText), ("goals_after_text", str afterText),
        ("goal_ids_before", toJson (ti.goalsBefore.map (fun g => g.name.toString))),
        ("goal_ids_after", toJson (ti.goalsAfter.map (fun g => g.name.toString))),
        ("goal_assignments_after", toJson assignments),
        ("trace_level", str "elaborator_tactic_event")])
      count.modify (· + 1))
  emit out (obj [("record_type", str "summary"), ("complete", toJson true),
    ("replay_success", toJson true), ("triads", toJson found),
    ("fragments", toJson (← count.get))])
  return 0

private unsafe def run (a : Args) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let path : System.FilePath := a.get "--output"
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.withFile path .write fun out => do
    if a.command == "trace" then return ← traceSource a out
    let modules := if (a.all "--module").isEmpty then #["OTSelector"] else a.all "--module"
    let imports := modules.map (fun m => { module := m.toName : Import })
    let env ← importModules imports options (loadExts := true) (level := .private)
    exportEnv a env out

end ProofAtlas

unsafe def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["help"] then
    IO.println ProofAtlas.help
    return 0
  match ProofAtlas.parseArgs args with
  | .error e => IO.eprintln e; return 2
  | .ok a =>
    try ProofAtlas.run a
    catch e => IO.eprintln s!"proof-atlas: {e}"; return 1
