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
The elaborator-side facts `scripts/fc_leaneval_importer.py` would otherwise
get by reading Lean with regular expressions.

Given a module and a declaration name, this prints JSON with what the
elaborated environment knows exactly and the text layer can only guess:

- the declaration's source range, for slicing its original text;
- its binders, with names and explicitness, for the Solution adapter;
- the type of each `sorry` inside the *statement*, which is the type of an
  `answer(sorry)` slot. The `answer_type` field in a `comparator/problems`
  file exists only because surface syntax does not carry this; the
  environment does.

Usage:
  lake exe comparator_facts <Module> <declaration>

The declaration may be given in full or by any whole suffix, the same rule
the Python importer uses.
-/

open Lean Meta

/-- A request matches a name in full, or by dropping any whole prefix. -/
def declares (declared : Name) (requested : String) : Bool :=
  let s := declared.toString
  s == requested || s.endsWith ("." ++ requested)

/-- Declaration parameters, as opposed to `∀` binders in the conclusion.

`theorem foo (n : Nat) : P n` lambda-abstracts `n` in its proof value;
`theorem foo : ∀ n : Nat, P n` does not. Only the former are applied by the
generated Solution adapter, and `forallTelescope` alone cannot tell them
apart: the lambda arity of the (sorry) value can. lean-eval's extractor
draws the same line for the same reason. -/
partial def lambdaArity : Expr → Nat
  | .lam _ _ b _ => lambdaArity b + 1
  | .mdata _ b => lambdaArity b
  | _ => 0

def binderJson (name : Name) (bi : BinderInfo) : Json :=
  Json.mkObj [("name", toJson name.toString), ("explicit", toJson bi.isExplicit)]

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.getD Name.anonymous).toString
  | none => ""

/-- Declared by this repository, as opposed to arriving with `import Mathlib`. -/
def isFCLocal (env : Environment) (n : Name) : Bool :=
  (moduleOf env n).startsWith "FormalConjectures"

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
    | none => (seen, acc)
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

unsafe def runWithImports {α : Type} (moduleNames : Array Name)
    (actionToRun : MetaM α) : IO α := do
  initSearchPath (← getBuildDir)
  let imports := moduleNames.map fun n => { module := n }
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  -- Twice the default budget, in the context's raw units, which are a
  -- thousand times the `maxHeartbeats` option's: 800000 here meant "800" and
  -- killed the first query. Finite, so a pathological statement errors and is
  -- caught rather than grinding forever, which maxHeartbeats := 0 did.
  let ctx := { fileName := "", fileMap := default, maxHeartbeats := 400000000 }
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

unsafe def main (args : List String) : IO UInt32 := do
  let [modName, declName] := args
    | IO.eprintln "usage: comparator_facts <Module> <declaration>"; return 1
  runWithImports #[modName.toName] do
    let env ← getEnv
    match resolveIn env modName.toName declName with
    | .error msg => IO.eprintln msg; return 1
    | .ok n => emit env n declName
where
  emit (env : Environment) (name : Name) (decl : String) : MetaM UInt32 := do
    let some info := env.find? name | IO.eprintln "vanished"; return 1
    let ranges ← findDeclarationRanges? name
    -- The statement's sorries are `answer(sorry)` slots; a proof's sorry is
    -- not in the *type*, so everything found here is a slot.
    -- `findAnswerExprs` is the repository's own detection: it reads the
    -- annotation the `answer` elaborator leaves, rather than guessing from
    -- `sorryAx` applications.
    let answerTypes ← forallTelescope info.type fun _ body => do
      let found := Google.findAnswerExprs body
      found.mapM fun a => do pure (toString (← ppExpr (← inferType a)))
    let arity := match info.value? with
      | some v => lambdaArity v
      | none => 0
    let binders ← forallTelescope info.type fun xs _ =>
      (xs.extract 0 arity).mapM fun x => do
        let d ← x.fvarId!.getDecl
        pure (binderJson d.userName d.binderInfo)
    let rangeJson := rangeToJson ranges
    -- Only the statement's dependencies: the proof is replaced by `sorry` in
    -- the generated Challenge, so nothing the value names has to be carried.
    let direct := info.type.getUsedConstants.filter (isFCLocal env)
    let (_, ordered) := direct.foldl (fun p c => fcOrder env c p.1 p.2)
      (({} : Std.HashSet Name), (#[] : Array Name))
    -- The equation compiler and `decide` leave constants like
    -- `Finset.greedySidon.aux._proof_1` and `.match_1` in the closure. They
    -- have no source range because they have no source: copying the parent
    -- declaration's text regenerates them. Emit them separately so the
    -- importer can check each one has an ancestor that is being copied,
    -- rather than dropping them silently.
    let mut deps := #[]
    let mut generated := #[]
    for d in ordered.filter (· != name) do
      match ← findDeclarationRanges? d with
      | some r =>
        deps := deps.push <| Json.mkObj [
          ("name", toJson d.toString),
          ("module", toJson (moduleOf env d)),
          ("range", rangeToJson (some r))]
      | none => generated := generated.push (toJson d.toString)
    -- The `@[category ...]` tag, spelled the way the attribute is written.
    -- lean-eval displays open conjectures apart from its evaluation set, so
    -- the importer needs to know which of the two a declaration is; the tag
    -- lives in the environment extension, not in anything the text layer
    -- could read reliably.
    let category := match (ProblemAttributes.categoryExt.getState env).toList.find?
        (·.declName == name) with
      | some tag => Json.str <| match tag.category with
        | .research .open => "research open"
        | .research .solved => "research solved"
        | .textbook => "textbook"
        | .test => "test"
        | .API => "API"
      | none => Json.null
    let payload := Json.mkObj [
      ("declaration", toJson decl),
      ("name", toJson name.toString),
      ("category", category),
      ("range", rangeJson),
      ("binders", toJson binders.toList),
      ("answerTypes", toJson answerTypes.toList),
      ("dependencies", toJson deps.toList),
      ("generatedDependencies", toJson generated.toList)]
    IO.println payload.pretty
    return 0
  rangeToJson (ranges : Option DeclarationRanges) : Json :=
    match ranges with
    | some r => Json.mkObj [
        ("startLine", toJson r.range.pos.line),
        ("startColumn", toJson r.range.pos.column),
        ("endLine", toJson r.range.endPos.line),
        ("endColumn", toJson r.range.endPos.column)]
    | none => Json.null
