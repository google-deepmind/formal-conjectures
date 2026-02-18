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
import FormalConjectures.Util.Attributes

open Lean ProblemAttributes

def getModuleNameFromFile (file : System.FilePath) : IO Name := do
  let components := file.withExtension "" |>.components
  -- Assuming the file is under FormalConjectures/ or FormalConjecturesForMathlib/
  let mut moduleComponents := []
  let mut found := false
  for c in components do
    if c == "FormalConjectures" || c == "FormalConjecturesForMathlib" || found then
      found := true
      moduleComponents := moduleComponents ++ [c]
  if moduleComponents.isEmpty then
    throw <| IO.userError s!"Could not determine module name for {file}. Is it under FormalConjectures/ or FormalConjecturesForMathlib/?"
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

def nameAny (n : Name) (p : String → Bool) : Bool :=
  match n with
  | .anonymous => false
  | .str p' s => p s || nameAny p' p
  | .num p' _ => nameAny p' p

def isInternal (n : Name) : Bool :=
  nameAny n (fun s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_")

def amsToNat (a : AMS) : Nat :=
  match a with
  | .«0» => 0 | .«1» => 1 | .«3» => 3 | .«5» => 5 | .«6» => 6 | .«8» => 8 | .«11» => 11
  | .«12» => 12 | .«13» => 13 | .«14» => 14 | .«15» => 15 | .«16» => 16 | .«17» => 17
  | .«18» => 18 | .«19» => 19 | .«20» => 20 | .«22» => 22 | .«26» => 26 | .«28» => 28
  | .«30» => 30 | .«31» => 31 | .«32» => 32 | .«33» => 33 | .«34» => 34 | .«35» => 35
  | .«37» => 37 | .«39» => 39 | .«40» => 40 | .«41» => 41 | .«42» => 42 | .«43» => 43
  | .«44» => 44 | .«45» => 45 | .«46» => 46 | .«47» => 47 | .«49» => 49 | .«51» => 51
  | .«52» => 52 | .«53» => 53 | .«54» => 54 | .«55» => 55 | .«57» => 57 | .«58» => 58
  | .«60» => 60 | .«62» => 62 | .«65» => 65 | .«68» => 68 | .«70» => 70 | .«74» => 74
  | .«76» => 76 | .«78» => 78 | .«80» => 80 | .«81» => 81 | .«82» => 82 | .«83» => 83
  | .«85» => 85 | .«86» => 86 | .«90» => 90 | .«91» => 91 | .«92» => 92 | .«93» => 93
  | .«94» => 94 | .«97» => 97

structure TheoremInfo where
  name : String
  file : String
  categories : List String
  subjects : List String
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
      let f2 ← getAllLeanFiles "FormalConjecturesForMathlib"
      pure (f1 ++ f2)
    | [file] => pure #[System.FilePath.mk file]
    | _ => throw <| IO.userError "Usage: extract_names [file]"
  
  let mut moduleToFile : Std.HashMap Name String := {}
  let mut moduleNames := #[]
  for file in leanFiles do
    try
      let modName ← getModuleNameFromFile file
      moduleNames := moduleNames.push modName
      moduleToFile := moduleToFile.insert modName file.toString
    catch _ => pure ()

  runWithImports moduleNames do
    let env ← getEnv
    let tags ← getTags
    let subjectTags ← getSubjectTags

    -- Create maps for quick lookup
    let mut categoryMap : Std.HashMap Name (List String) := {}
    for tag in tags do
      categoryMap := categoryMap.insert tag.declName (categoryToString tag.category :: categoryMap.getD tag.declName [])

    let mut subjectMap : Std.HashMap Name (List String) := {}
    for tag in subjectTags do
      let subjects := tag.subjects.map (fun (s : AMS) => s!"{amsToNat s}")
      subjectMap := subjectMap.insert tag.declName (subjects ++ subjectMap.getD tag.declName [])

    let mut allResults : List TheoremInfo := []
    for modName in moduleNames do
      let some modIdx := env.header.moduleNames.findIdx? (· == modName)
        | continue
      let modData := env.header.moduleData[modIdx]!
      let fileName := moduleToFile.getD modName "unknown"
      for info in modData.constants do
        let name := info.name
        match info with
        | ConstantInfo.thmInfo .. => 
          if !isInternal name then
            let cats := categoryMap.getD name []
            let subjs := subjectMap.getD name []
            if !cats.isEmpty || !subjs.isEmpty then
              allResults := { name := name.toString, file := fileName, categories := cats, subjects := subjs } :: allResults
        | _ => pure ()
    
    IO.println (toJson allResults.reverse).pretty
