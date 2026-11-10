import Lean

/-! Validation tooling only. Inventory is the actual kernel environment, not
source regexes or pre-existing #check commands. Legacy import loads private
module data. Each inventory item receives the real #check/#print axioms pair. -/
open Lean Elab Command Meta

/-- Once per whole-tree session, independently compare the fast module-data
inventory with every attributed constant in the actual kernel environment.
This guards against omissions without rescanning all Mathlib for each module. -/
elab "#verify_full_tree_inventory" "[" targets:ident,* "]" "to" output:str : command => do
  let wanted := targets.getElems.map (·.getId)
  let env := (← getEnv).setExporting false
  let mut selected : Std.HashSet Name := {}
  for n in wanted do
    unless env.allImportedModuleNames.contains n do
      throwError "Requested inventory module is not imported: {n}"
    if selected.contains n then
      throwError "Duplicate requested inventory module: {n}"
    selected := selected.insert n
  let mut actual : Std.HashMap Name (Array Name) := {}
  let mut total : Nat := 0
  for (n, _) in env.constants.toList do
    total := total + 1
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if selected.contains mod then
        actual := actual.insert mod ((actual.getD mod #[]).push n)
  let mut rows : Array Json := #[]
  for mod in wanted do
    let some idx := env.allImportedModuleNames.findIdx? (· == mod)
      | throwError "Missing imported inventory module: {mod}"
    let fast := env.header.moduleData[idx]!.constNames.filterMap fun n =>
      match env.getModuleIdxFor? n with
      | some i =>
        if env.allImportedModuleNames[i.toNat]! == mod && (env.find? n).isSome then some n else none
      | none => none
    let fast := fast.qsort Name.lt
    let slow := (actual.getD mod #[]).qsort Name.lt
    unless fast == slow do
      throwError "Module-data inventory differs from full kernel scan: {mod}"
    rows := rows.push <| Json.mkObj [
      ("module", toJson mod.toString), ("matches_full_kernel_scan", toJson true),
      ("declarations", toJson slow.size), ("kernel_names", toJson (slow.map Name.toString))]
  liftIO <| IO.FS.writeFile (System.FilePath.mk output.getString) <| (Json.mkObj [
    ("all_match", toJson true), ("scanned_kernel_constants", toJson total),
    ("module_count", toJson wanted.size), ("modules", toJson rows)]).pretty
  logInfo m!"FULL_TREE_INVENTORY_EQUIVALENT {wanted.size} modules; {total} kernel constants scanned"

elab "#fast_full_tree_audit " target:ident " to " output:str : command => do
  let wanted := target.getId
  let env := (← getEnv).setExporting false
  let some moduleIndex := env.allImportedModuleNames.findIdx? (· == wanted)
    | throwError "Requested audit module is not imported: {wanted}"
  -- ModuleData.constNames is the kernel import inventory, including private constants.
  -- Filter attribution exactly as the original full-environment scan did.
  let names := env.header.moduleData[moduleIndex]!.constNames.filterMap fun n =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if env.allImportedModuleNames[idx.toNat]! == wanted && (env.find? n).isSome then some n else none
    | none => none
  liftIO <| IO.eprintln s!"FAST_AUDIT_INVENTORY {wanted} {names.size}"
  let names := names.qsort Name.lt
  unless env.allImportedModuleNames.contains wanted do
    throwError "Requested audit module is not imported: {wanted}"
  let mut rows : Array Json := #[]
  for n in names do
    let some ci := env.find? n | throwError "Missing enumerated declaration: {n}"
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let ty ← liftTermElabM do
      let t ← inferType (mkConst n (ci.levelParams.map Level.param))
      unless ← isDefEq t ci.type do
        throwError "Stored/inferred type mismatch for {n}"
      return (← ppExpr t).pretty
    let axs ← collectAxioms n
    let id := mkIdent n
    logInfo m!"FULL_TREE_PAIR_BEGIN {n}"
    elabCommand (← `(#check $id))
    elabCommand (← `(#print axioms $id))
    logInfo m!"FULL_TREE_PAIR_END {n}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("user_name", toJson (privateToUserName n).toString),
      ("module", toJson wanted.toString),
      ("kind", toJson kind),
      ("private", toJson (isPrivateName n)),
      ("internal_detail", toJson n.isInternalDetail),
      ("universes", toJson (ci.levelParams.map Name.toString)),
      ("type", toJson ty),
      ("axioms", toJson ((axs.qsort Name.lt).map Name.toString)),
      ("builtin_check_and_print_axioms_invoked", toJson true)]
  let result := Json.mkObj [
    ("module", toJson wanted.toString),
    ("enumeration", toJson "all kernel constants attributed to imported module; private view"),
    ("environment_constant_count", toJson names.size),
    ("records", toJson rows)]
  liftIO <| IO.FS.writeFile (System.FilePath.mk output.getString) result.pretty
  logInfo m!"FULL_TREE_AUDIT_DONE {wanted} {names.size}"
