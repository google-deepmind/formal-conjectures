/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.Util.Attributes.Basic

open Lean ProblemAttributes

def getModuleNameFromFile (file : System.FilePath) : IO Name := do
  let components := file.withExtension "" |>.components
  -- Assuming the file is under FormalConjectures/
  let mut moduleComponents := []
  let mut found := false
  for c in components do
    if c == "FormalConjectures" || found then
      found := true
      moduleComponents := moduleComponents ++ [c]
  if moduleComponents.isEmpty then
    throw <| IO.userError s!"Could not determine module name for {file}. Is it under FormalConjectures/?"
  return moduleComponents.foldl (fun n s => Name.mkStr n s) Name.anonymous

-- Helper to format Category as string
def categoryToString : Category → String
  | .highSchool => "high_school"
  | .undergraduate => "undergraduate"
  | .graduate => "graduate"
  | .research .open => "research open"
  | .research .solved => "research solved"
  | .research (.formallySolvedAt _ _) => "research formally solved"
  | .test => "test"
  | .API => "API"

-- Helper to format FormalProofKind as string
def formalProofKindToString : FormalProofKind → String
  | .formalConjecturesProof => "formal_conjectures"
  | .lean4 => "lean4"
  | .otherSystem => "other_system"

def nameAny (n : Name) (p : String → Bool) : Bool :=
  match n with
  | .anonymous => false
  | .str p' s => p s || nameAny p' p
  | .num p' _ => nameAny p' p

def isInternal (n : Name) : Bool :=
  nameAny n (fun s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_")

structure TheoremInfo where
  «theorem» : String
  module : String
  category : String
  subjects : List String
  statement : String
  docstring : Option String
  formalProofKind : Option String
  formalProofLink : Option String
  deriving ToJson

unsafe def runWithImports {α : Type} (moduleNames : Array Name) (actionToRun : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  let imports := moduleNames.map fun n => { module := n }
  let currentCtx := { fileName := "", fileMap := default }
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  let (result, _newState) ← Core.CoreM.toIO actionToRun currentCtx { env := env }
  return result

partial def getAllLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  if ← dir.isDir then
    for entry in ← dir.readDir do
      if ← entry.path.isDir then
        files := files ++ (← getAllLeanFiles entry.path)
      else if entry.path.extension == some "lean" then
        files := files.push entry.path
  return files

unsafe def main (args : List String) : IO Unit := do
  let leanFiles ← match args with
    | [] =>
      let f1 ← getAllLeanFiles "FormalConjectures"
      pure (f1)
    | [file] => pure #[System.FilePath.mk file]
    | _ => throw <| IO.userError "Usage: extract_names [file]"

  let mut moduleNames := #[]
  for file in leanFiles do
    try
      let modName ← getModuleNameFromFile file
      moduleNames := moduleNames.push modName
    catch _ => pure ()

  runWithImports moduleNames do
    let env ← getEnv
    let tags ← getTags
    let subjectTags ← getSubjectTags

    -- Create maps for quick lookup
    let mut categoryMap : Std.HashMap Name (List String) := {}
    let mut categoryFullMap : Std.HashMap Name CategoryTag := {}
    for tag in tags do
      categoryMap := categoryMap.insert tag.declName (categoryToString tag.category :: categoryMap.getD tag.declName [])
      categoryFullMap := categoryFullMap.insert tag.declName tag

    let mut subjectMap : Std.HashMap Name (List String) := {}
    for tag in subjectTags do
      let subjects := tag.subjects.map (fun (s : AMS) => s!"{s.toNat?.get!}")
      subjectMap := subjectMap.insert tag.declName (subjects ++ subjectMap.getD tag.declName [])

    let mut allResults : List TheoremInfo := []
    for modName in moduleNames do
      let some modIdx := env.header.moduleNames.findIdx? (· == modName)
        | continue
      let modData := env.header.moduleData[modIdx]!
      for info in modData.constants do
        let name := info.name
        match info with
        | ConstantInfo.thmInfo .. =>
          if !isInternal name then
            let cats := categoryMap.getD name []
            let subjs := subjectMap.getD name []
            if !cats.isEmpty || !subjs.isEmpty then
              if cats.length ≠ 1 then
                throwError m!"Theorem {name} must have exactly one category, found {cats.length}."
              let statement := toString (← Meta.MetaM.run' (Meta.ppExpr info.type))
              let docstring ← findDocString? env name
              let (formalProofKind, formalProofLink) :=
                if let some tag := categoryFullMap.get? name then
                  if let .research (.formallySolvedAt kind link) := tag.category then
                    (some (formalProofKindToString kind), some link)
                  else
                    (none, none)
                else
                  (none, none)
              allResults := {
                «theorem» := name.toString,
                module := modName.toString,
                category := cats.head!,
                subjects := subjs,
                statement := statement,
                docstring := docstring,
                formalProofKind := formalProofKind,
                formalProofLink := formalProofLink
              } :: allResults
        | _ => pure ()

    -- Collect module docstrings via Lean's getModuleDoc? API
    let mut moduleDocstrings : List (String × String) := []
    for modName in moduleNames do
      if let some docs := getModuleDoc? env modName then
        if docs.size != 1 then
          IO.eprintln s!"WARNING: Module {modName} has {docs.size} module docstrings"
        if docs.size > 0 then
          let combined := "\n\n".intercalate (docs.toList.map (·.doc))
          moduleDocstrings := (modName.toString, combined) :: moduleDocstrings

    -- Build structured output: { problems: [...], moduleDocstrings: {...} }
    let problemsJson := toJson allResults.reverse
    let moduleDocJson := Json.mkObj (moduleDocstrings.reverse.map fun (k, v) => (k, toJson v))
    let output := Json.mkObj [
      ("problems", problemsJson),
      ("moduleDocstrings", moduleDocJson)
    ]
    IO.println output.pretty
