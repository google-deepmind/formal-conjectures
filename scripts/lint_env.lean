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
module

public import Lean
public import Batteries.Tactic.Lint
public meta import FormalConjecturesUtil.EnvLinters

/-!
# Lint the environment

Runs this repository's environment linters (see `FormalConjecturesUtil.EnvLinters`) on every
declaration of the given problem files, or of all of `FormalConjectures/`.

The script reads the compiled `.olean` files, so build the problems first.
```bash
lake build
lake exe lint_env [directory-or-file]
```
Exits with status 1 if a linter reports something.
-/

@[expose] public meta section

open Lean Batteries.Tactic.Lint

def getModuleNameFromFile (file : System.FilePath) : IO Name := do
  let components := file.withExtension "" |>.components
  let mut moduleComponents := []
  let mut found := false
  for c in components do
    if c == "FormalConjectures" || found then
      found := true
      moduleComponents := moduleComponents ++ [c]
  if moduleComponents.isEmpty then
    throw <| IO.userError s!"Could not determine module name for {file}. Is it under FormalConjectures/?"
  return moduleComponents.foldl (fun n s => Name.mkStr n s) Name.anonymous

partial def getAllLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  if ← dir.isDir then
    for entry in ← dir.readDir do
      if ← entry.path.isDir then
        files := files ++ (← getAllLeanFiles entry.path)
      else if entry.path.extension == some "lean" then
        files := files.push entry.path
  return files

/-- The linters of `FormalConjecturesUtil.EnvLinters`, by their short names. -/
def linterNames : List Name :=
  [`researchOpenSorryFree, `valueQuestionTag, `foreignAnswer, `statementSorry]

unsafe def main (args : List String) : IO UInt32 := do
  let leanFiles ← match args with
    | [] => getAllLeanFiles "FormalConjectures"
    | [arg] =>
      let p := System.FilePath.mk arg
      if ← p.isDir then getAllLeanFiles p else pure #[p]
    | _ => throw <| IO.userError "Usage: lint_env [directory-or-file]"
  let moduleNames ← leanFiles.mapM getModuleNameFromFile
  initSearchPath (← getBuildDir)
  Lean.enableInitializersExecution
  let env ← Lean.importModules (moduleNames.map ({ module := · })) {} (trustLevel := 1024)
    (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let (code, _) ← Core.CoreM.toIO (ctx := ctx) (s := { env := env }) do
    -- every declaration of the given modules
    let mut decls := #[]
    for modName in moduleNames do
      let some modIdx := env.header.moduleNames.findIdx? (· == modName) | continue
      for info in env.header.moduleData[modIdx]!.constants do
        decls := decls.push info.name
    let linters ← getChecks (slow := true) (runOnly := some linterNames) (runAlways := none)
    let results ← lintCore decls linters (inIO := true)
    if results.any (!·.2.isEmpty) then
      let msg ← formatLinterResults results decls (groupByFilename := true)
        (useErrorFormat := true) "in FormalConjectures" (runSlowLinters := true) .medium
        linters.size
      IO.println (← msg.toString)
      return (1 : UInt32)
    else
      IO.println s!"-- Linting passed for {decls.size} declarations in {moduleNames.size} modules."
      return 0
  return code
