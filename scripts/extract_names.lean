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

/-- Valid keys for the `--exclude` flag. -/
def validExcludeKeys : List String :=
  ["docstring", "statement", "subjects", "formalProofKind", "formalProofLink", "moduleDocstrings"]

structure TheoremInfo where
  «theorem» : String
  module : String
  category : String
  subjects : List String
  statement : String
  docstring : Option String
  formalProofKind : Option String
  formalProofLink : Option String


/-- Serialize `TheoremInfo` to JSON, omitting fields whose keys are in `exclude`. -/
def TheoremInfo.toFilteredJson (info : TheoremInfo) (exclude : Std.HashSet String := {}) : Json :=
  let fields : List (String × Json) :=
    [("theorem", toJson info.theorem),
     ("module", toJson info.module),
     ("category", toJson info.category)]
    ++ (if exclude.contains "subjects" then [] else [("subjects", toJson info.subjects)])
    ++ (if exclude.contains "statement" then [] else [("statement", toJson info.statement)])
    ++ (if exclude.contains "docstring" then [] else [("docstring", toJson info.docstring)])
    ++ (if exclude.contains "formalProofKind" then [] else
        [("formalProofKind", toJson info.formalProofKind)])
    ++ (if exclude.contains "formalProofLink" then [] else
        [("formalProofLink", toJson info.formalProofLink)])
  Json.mkObj fields

instance : ToJson TheoremInfo where
  toJson info := info.toFilteredJson

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
  -- Parse flags vs file arguments
  let (flags, fileArgs) := args.partition (·.startsWith "--")
  let mut excludeSet : Std.HashSet String := {}
  for flag in flags do
    if flag == "--no-docstrings" then
      excludeSet := excludeSet.insert "docstring" |>.insert "moduleDocstrings"
    else if flag.startsWith "--exclude=" then
      let excludeStr := flag.drop 10 |>.toString
      let fields := excludeStr.splitOn ","
      for f in fields do
        if f ∉ validExcludeKeys then
          throw <| IO.userError s!"Unknown exclude key: '{f}'. Valid keys: {validExcludeKeys}"
        excludeSet := excludeSet.insert f
    else
      throw <| IO.userError s!"Unknown flag: '{flag}'. Supported: --exclude=key1,key2 --no-docstrings"
  let leanFiles ← match fileArgs with
    | [] =>
      let f1 ← getAllLeanFiles "FormalConjectures"
      pure (f1)
    | [arg] =>
      let p := System.FilePath.mk arg
      if ← p.isDir then
        getAllLeanFiles p
      else
        pure #[p]
    | _ => throw <| IO.userError "Usage: extract_names [directory-or-file] [--exclude=key1,key2] [--no-docstrings]"

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
    let formalProofTags ← getFormalProofTags

    -- Create maps for quick lookup
    let mut categoryMap : Std.HashMap Name (List String) := {}
    let mut categoryFullMap : Std.HashMap Name CategoryTag := {}
    for tag in tags do
      categoryMap := categoryMap.insert tag.declName (categoryToString tag.category :: categoryMap.getD tag.declName [])
      categoryFullMap := categoryFullMap.insert tag.declName tag

    -- Create formal proof map
    let mut formalProofMap : Std.HashMap Name FormalProofTag := {}
    for tag in formalProofTags do
      formalProofMap := formalProofMap.insert tag.declName tag

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
              if docstring.isNone then
                IO.eprintln s!"WARNING: Theorem {name} (category: {cats.head!}) is missing a docstring"
              -- Extract formal proof info from the separate formal_proof attribute
              let (formalProofKind, formalProofLink) :=
                if let some tag := formalProofMap.get? name then
                  (some (formalProofKindToString tag.proofKind), some tag.proofLink)
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
    if !excludeSet.contains "moduleDocstrings" then
      for modName in moduleNames do
        if let some docs := getModuleDoc? env modName then
          if docs.size != 1 then
            IO.eprintln s!"WARNING: Module {modName} has {docs.size} module docstrings"
          if docs.size > 0 then
            let combined := "\n\n".intercalate (docs.toList.map (·.doc))
            moduleDocstrings := (modName.toString, combined) :: moduleDocstrings

    -- Build structured output: { problems: [...], moduleDocstrings: {...} }
    let problemsJson := toJson (allResults.reverse.map (·.toFilteredJson excludeSet))
    let mut outputFields : List (String × Json) := [("problems", problemsJson)]
    if !excludeSet.contains "moduleDocstrings" then
      let moduleDocJson := Json.mkObj (moduleDocstrings.reverse.map fun (k, v) => (k, toJson v))
      outputFields := outputFields ++ [("moduleDocstrings", moduleDocJson)]
    let output := Json.mkObj outputFields
    IO.println output.pretty
