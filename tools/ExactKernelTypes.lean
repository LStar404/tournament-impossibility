import Lean

/-! Independent full expression export. `reprStr` uses the derived `Repr Expr`
instance on the stored type, not the pretty-printer, and therefore does not hide
proof terms or abbreviate implicit arguments. All expression constructors,
binder names/info, constants/universes and metadata are included. -/
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

elab "#exact_kernel_types" "[" targets:ident,* "]" "to" output:str : command => do
  let env := (← getEnv).setExporting false
  let mut count := 0
  for target in targets.getElems do
    let wanted := target.getId
    let some idx := env.allImportedModuleNames.findIdx? (· == wanted)
      | throwError "Missing module: {wanted}"
    let names := (env.header.moduleData[idx]!.constNames.filterMap fun n =>
      match env.getModuleIdxFor? n with
      | some i =>
        if env.allImportedModuleNames[i.toNat]! == wanted && (env.find? n).isSome then some n else none
      | none => none).qsort Name.lt
    let mut rows : Array Json := #[]
    for n in names do
      let some ci := env.find? n | throwError "Missing declaration: {n}"
      rows := rows.push <| Json.mkObj [
        ("name", toJson n.toString),
        ("universes", toJson (ci.levelParams.map Name.toString)),
        ("type_expr_repr", toJson (reprStr ci.type))]
      count := count + 1
    let file := System.FilePath.mk output.getString / (wanted.toString ++ ".json")
    liftIO <| IO.FS.writeFile file <| (Json.mkObj [
      ("module", toJson wanted.toString), ("count", toJson rows.size),
      ("representation", toJson "Lean derived Repr Expr; includes proof terms, universes, binder info and metadata"),
      ("records", toJson rows)]).compress
  logInfo m!"EXACT_KERNEL_TYPES_DONE {targets.getElems.size} {count}"
