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
module

public import Lean
public meta import FormalConjecturesUtil.ProblemMetadata

/-!
# Extract Names

This script extracts metadata (theorem names, statements, categories, subjects,
formal proof links, and answer kinds) from formalized mathematical conjectures
in the repository.

### Usage
```bash
# Compile with postpone setting for answerKind extraction
lake build FormalConjecturesAnswerPostpone
lake exe extract_names [directory-or-file] [--exclude=key1,key2] [--no-docstrings]
```

**IMPORTANT NOTE**: Make sure to build with `lake build FormalConjecturesAnswerPostpone`
before running this script. This compiles the library under `weak.google.answer = "postpone"`
mode, allowing `extract_names` to correctly locate and extract `answerKinds` (Prop vs
non-Prop answer metadata). Otherwise, `answer(sorry)` simplifies to `True` during
default elaboration, and `answerKinds` will always be extracted as `[]` for `Prop`
valued answers.
-/

@[expose] public meta section

open Lean FormalConjectures.Metadata

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

/-- Run a git command and return its stdout, trimmed. Returns `none` on failure. -/
def gitOutput (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "git", args := args }
    if out.exitCode == 0 then
      let s := out.stdout.trimAscii.toString
      return if s.isEmpty then none else some s
    else return none
  catch _ => return none

/-- Get the ISO 8601 timestamp of when a file was first added to the repo. -/
def getFileFirstAdded (file : System.FilePath) : IO (Option String) :=
  gitOutput #["log", "--diff-filter=A", "--follow", "--format=%aI", "--", file.toString]
    <&> (·.bind (·.splitOn "\n" |>.getLast?))

/-- Get the ISO 8601 timestamp of the most recent commit that modified a file. -/
def getFileLastModified (file : System.FilePath) : IO (Option String) :=
  gitOutput #["log", "-1", "--format=%aI", "--", file.toString]

/-- Valid keys for the `--exclude` flag. -/
def validExcludeKeys : List String :=
  ["docstring", "statement", "subjects", "formalProofs",
   "hasSorryFreeProof", "moduleDocstrings", "answerKinds",
   "fileFirstAdded", "fileLastModified"]

unsafe def runWithImports {α : Type} (moduleNames : Array Name) (actionToRun : CoreM α) : IO α := do
  initSearchPath (← getBuildDir)
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
    | _ =>
      let usageMsg :=
        "Usage: extract_names [directory-or-file] [--exclude=key1,key2] [--no-docstrings]\n\n" ++
        "Note: Make sure to run `lake build FormalConjecturesAnswerPostpone` before running " ++
        "this script so that `answerKind` metadata is extracted correctly."
      throw <| IO.userError usageMsg

  -- Pre-compute git timestamps for each file and build module name array (only when not excluded)
  let needFirstAdded := !excludeSet.contains "fileFirstAdded"
  let needLastModified := !excludeSet.contains "fileLastModified"
  let needGitInfo := needFirstAdded || needLastModified
  let mut moduleNames := #[]
  let mut fileTimestamps : Std.HashMap Name (Option String × Option String) := {}
  for file in leanFiles do
    try
      let modName ← getModuleNameFromFile file
      moduleNames := moduleNames.push modName
      if needGitInfo then
        let firstAdded ← if needFirstAdded then getFileFirstAdded file else pure none
        let lastModified ← if needLastModified then getFileLastModified file else pure none
        fileTimestamps := fileTimestamps.insert modName (firstAdded, lastModified)
    catch _ => pure ()

  runWithImports moduleNames do
    let env ← getEnv
    let allResults ← extractProblems moduleNames fileTimestamps

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
    let problemsJson := toJson (allResults.map (·.toFilteredJson excludeSet))
    -- Consumers should not have to guess whether they are reading the old
    -- `formalProofKind` shape or the `formalProofs` list; say so.
    let mut outputFields : List (String × Json) :=
      [("schemaVersion", Lean.toJson (2 : Nat)), ("problems", problemsJson)]
    if !excludeSet.contains "moduleDocstrings" then
      let moduleDocJson := Json.mkObj (moduleDocstrings.reverse.map fun (k, v) => (k, toJson v))
      outputFields := outputFields ++ [("moduleDocstrings", moduleDocJson)]
    let output := Json.mkObj outputFields
    IO.println output.pretty
