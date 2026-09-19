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

/-!
# Environment extraction

What the elaborated environment knows about a declaration: which FC-local
constants it needs and in what order, how a requested name resolves within a
module, and the binder facts the importer emits.
-/

open Lean Meta

/-- A request matches a name in full, or by dropping any whole prefix. -/
def declares (declared : Name) (requested : String) : Bool :=
  let s := declared.toString
  s == requested || s.endsWith ("." ++ requested)

def binderJson (name : Name) (bi : BinderInfo) : Json :=
  Json.mkObj [("name", toJson name.toString), ("explicit", toJson bi.isExplicit)]

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.getD Name.anonymous).toString
  | none => ""

/-- Declared by this repository, as opposed to arriving with `import Mathlib`.

A constant with a module index the environment cannot name answers `true`
here rather than `false`. Both answers are wrong in that case, but they fail
in opposite directions: `false` means "arrives with Mathlib, copy nothing",
which drops it from `ChallengeDeps` and is caught only by elaborating the
result, while `true` means "copy it", and a constant with no source range is
reported as a generated dependency, which the importer refuses unless a
copied ancestor explains it. Fail towards the check that exists. -/
def isFCLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some name => name.toString.startsWith "FormalConjectures"
    | none => true
  | none => false

/-- The FC-local constants a declaration needs, dependencies before dependents.

Post-order over the dependency graph, expanding through both the type and the
value of each FC-local constant: a definition's body names constants its type
does not, and `ChallengeDeps` has to carry them or the copy will not elaborate.
Mathlib and core constants are not expanded, since they arrive with
`import Mathlib`. -/
partial def fcOrder (env : Environment) (n : Name)
    (seen : Std.HashSet Name) (acc : Array Name) : Std.HashSet Name × Array Name :=
  if seen.contains n then (seen, acc) else
    let seen := seen.insert n
    match env.find? n with
    -- Reached as a used constant but absent from the environment. Keeping it
    -- costs a generated-dependency entry the importer will question; dropping
    -- it costs a `ChallengeDeps` that is short by one declaration and says
    -- nothing about it.
    | none => (seen, acc.push n)
    | some info =>
      let fromValue := match info.value? with
        | some v => v.getUsedConstants
        | none => #[]
      -- An inductive has no value, and its fields live in the constructor
      -- rather than in its own type: `structure EdgeN (N D : Nat) where u : V N`
      -- has type `Nat → Nat → Type`, which never mentions `V`. Without the
      -- constructors here the closure still contains `V`, reached some other
      -- way, but orders it after `EdgeN`, and the copy does not elaborate.
      let fromCtors := match info with
        | .inductInfo val => val.ctors.toArray
        | _ => #[]
      let children := (info.type.getUsedConstants ++ fromValue ++ fromCtors).filter
        fun c => isFCLocal env c && c != n
      let (seen, acc) := children.foldl (fun p c => fcOrder env c p.1 p.2) (seen, acc)
      (seen, acc.push n)

/-- One declaration's heartbeat budget, in the context's raw units. A batch
caller multiplies this by its pair count rather than restating it. -/
def heartbeatsPerDeclaration : Nat := 400000000

unsafe def runWithImports {α : Type} (moduleNames : Array Name)
    (actionToRun : MetaM α) (heartbeats : Nat := heartbeatsPerDeclaration) : IO α := do
  initSearchPath (← getBuildDir)
  let imports := moduleNames.map fun n => { module := n }
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  -- Twice the default budget, in the context's raw units, which are a
  -- thousand times the `maxHeartbeats` option's: 800000 here meant "800" and
  -- killed the first query. Finite, so a pathological statement errors and is
  -- caught rather than grinding forever, which maxHeartbeats := 0 did. A
  -- batch caller scales the budget by its pair count, since one context
  -- meters the whole action.
  let ctx := { fileName := "", fileMap := default, maxHeartbeats := heartbeats }
  let (result, _) ← Core.CoreM.toIO (actionToRun.run' {} {}) ctx { env := env }
  return result

/-- Resolve within one module. Names declared elsewhere are not candidates,
which is what lets one environment holding every module still disambiguate
`conjecture_1_1` the way a per-module import does. -/
def resolveIn (env : Environment) (modName : Name) (declName : String) :
    Except String Name :=
  let inModule (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]? == some modName
    | none => false
  -- No `isInternal` filter: `erdos_340.variants._33_mem_sub` has a component
  -- starting with an underscore, which that heuristic calls internal. The
  -- whole-suffix rule in `declares` already keeps auxiliary declarations out,
  -- since `foo.proof_1` is not a suffix match for `foo`.
  let matches_ := env.constants.toList.filterMap fun (n, _) =>
    if declares n declName && inModule n then some n else none
  match matches_ with
  | [] => .error s!"{declName} not found in {modName}"
  | [n] => .ok n
  | _ =>
    match matches_.filter (·.toString == declName) with
    | [n] => .ok n
    | _ => .error s!"{declName} is ambiguous: {matches_}"
