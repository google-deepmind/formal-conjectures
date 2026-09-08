/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic

/-!
# Package-backed problem export

Elaborate an FC source module with answers postponed, then export its target type.
Dependencies remain references to the pinned source package. No source fragments
or surrounding scopes are copied into the exported declaration.
-/

open Lean Meta Elab

namespace ExportProblem

structure Hole where
  name : Name
  type : Expr
  original : Expr
  levels : List Name

private def printOptions (opts : Options) : Options :=
  opts.setBool `pp.fullNames true |>.setBool `pp.notation false
    |>.setBool `pp.explicit true |>.setBool `pp.universes true
    |>.setBool `pp.proofs true |>.setBool `pp.deepTerms true
    |>.setBool `pp.fieldNotation false |>.setBool `pp.funBinderTypes true |>.set `pp.width (100 : Nat)

/-- Reparse and elaborate the printed type, refusing a change in meaning. -/
private def renderType (type : Expr) : Term.TermElabM String := do
  Term.withLevelNames (collectLevelParams {} type).params.toList <|
   withOptions printOptions <|
   withTheReader Core.Context (fun ctx => { ctx with currNamespace := .anonymous, openDecls := [] }) do
    let text := (← ppExpr type).pretty
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term text
    let parsed ← Term.elabType stx
    Term.synthesizeSyntheticMVarsNoPostponing
    let parsed ← instantiateMVars parsed
    if parsed.hasExprMVar || !(← isDefEq type parsed) then
      throwError "Exported type failed its elaboration round trip:\n{text}"
    return text

private def exportType (name : Name) : Term.TermElabM Json := do
  let info ← getConstInfo name
  unless info matches .thmInfo _ do
    throwError "The target must be a theorem"
  let (type, holes) ← (Meta.transform info.type (pre := fun e => do
    let .mdata annotation inner := e | return .continue
    unless annotation.contains `answer do return .continue
    unless inner.hasSorry do return .visit inner
    let type ← inferType inner
    let used ← (Lean.collectFVars {} type).addDependencies
    let xs := (← getLCtx).getFVars.filter fun x => used.fvarSet.contains x.fvarId!
    let holeType ← mkForallFVars xs type
    let original ← mkLambdaFVars xs inner
    let holes ← getThe (Array Hole)
    let holeName := Name.mkSimple s!"fc_answer_{holes.size}"
    if (← getEnv).contains holeName then throwError "Export name collision: {holeName}"
    let levels := (collectLevelParams {} holeType).params.toList
    addDecl <| .defnDecl {
      name := holeName, levelParams := levels, type := holeType
      value := ← mkSorry holeType false
      hints := .opaque, safety := .safe
    }
    modifyThe (Array Hole) (·.push ⟨holeName, holeType, original, levels⟩)
    return .done <| mkAppN (.const holeName (levels.map Level.param)) xs
    ) : StateRefT (Array Hole) Term.TermElabM Expr).run #[]
  -- Substitute the original answers back before comparing to the source type.
  let restored := type.replace fun e => match e with
    | .const n levels => holes.find? (·.name == n) |>.map fun h =>
        h.original.instantiateLevelParams h.levels levels
    | _ => none
  unless ← isDefEq restored info.type do
    throwError "Answer abstraction changed the source statement"
  if type.hasSorry then
    throwError "The statement contains a sorry outside a supported answer slot"
  let mut declarations := #[]
  for h in holes do
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson h.name.toString), ("kind", toJson "def"),
      ("type", toJson (← renderType h.type)), ("levels", toJson h.levels)]
  declarations := declarations.push <| Json.mkObj [
    ("name", toJson "fc_problem"), ("kind", toJson "theorem"),
    ("type", toJson (← renderType type)), ("levels", toJson info.levelParams)]
  let category := (ProblemAttributes.categoryExt.getState (← getEnv)).toList.find?
    (·.declName == name)
  let category := category.map fun tag => match tag.category with
    | .research .open => "research open"
    | .research .solved => "research solved"
    | .textbook => "textbook"
    | .test => "test"
    | .API => "API"
  return Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("declaration", toJson name.toString),
    ("category", toJson category), ("declarations", toJson declarations)]

private partial def elaborateThrough (target : Name) : Frontend.FrontendM Unit := do
  let done ← Frontend.processCommand
  let state ← Frontend.getCommandState
  if state.messages.hasErrors then
    for message in state.messages.toList do
      if message.severity == .error then IO.eprintln (← message.toString)
    throw <| IO.userError "Source elaboration failed"
  if state.env.contains target then return
  if done then throw <| IO.userError s!"Declaration {target} was not found"
  elaborateThrough target

unsafe def main (args : List String) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    enableInitializersExecution
    if let ["--list-set", moduleName, declaration] := args then
      let env ← importModules #[{ module := moduleName.toName }] {} (loadExts := true)
      let names ← IO.ofExcept <| env.evalConst (List Name) {} declaration.toName false
      let entries ← names.toArray.mapM fun name => do
        let some index := env.getModuleIdxFor? name
          | throw <| IO.userError s!"No source module for {name}"
        let module := env.allImportedModuleNames[index.toNat]!
        return Json.mkObj [("declaration", toJson name.toString), ("module", toJson module.toString),
          ("path", toJson (String.intercalate "/" (module.components.map fun n => n.getString!) ++ ".lean"))]
      IO.println (toJson entries).pretty
      return 0
    let [path, moduleName, declaration] := args
      | throw <| IO.userError "usage: export_problem SOURCE MODULE DECLARATION"
    let input ← IO.FS.readFile path
    let context := Parser.mkInputContext input path
    let (header, parserState, messages) ← Parser.parseHeader context
    let opts := ({} : Options).set `google.answer ("postpone" : String)
      |>.setBool `autoImplicit false |>.set `maxRecDepth (4096 : Nat)
      |>.set `maxHeartbeats (800000 : Nat)
    let (env, messages) ← processHeader header opts messages context
      (mainModule := moduleName.toName)
    if env.contains declaration.toName then
      throw <| IO.userError "The target is imported rather than declared in the source module"
    let initial : Frontend.State := {
      commandState := Command.mkState env messages opts, parserState, cmdPos := parserState.pos }
    let (_, state) ← (elaborateThrough declaration.toName).run { inputCtx := context } |>.run initial
    let (result, _) ← (Frontend.runCommandElabM <| Command.liftTermElabM <|
      exportType declaration.toName).run { inputCtx := context } |>.run state
    IO.println result.pretty
    return 0
  catch error =>
    IO.eprintln s!"export_problem: {error}"
    return 1

end ExportProblem

unsafe def main (args : List String) : IO UInt32 := ExportProblem.main args
