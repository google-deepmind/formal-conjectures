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
The elaborator-side facts `make_comparator_workspace.py` currently gets by
reading Lean with regular expressions.

Given a module and a declaration name, this prints JSON with what the
elaborated environment knows exactly and the text layer can only guess:

- the declaration's source range, for slicing its original text;
- its binders, with names and explicitness, for the Solution adapter;
- the type of each `sorry` inside the *statement*, which is the type of an
  `answer(sorry)` slot. The generator's manifest `answer_type` field exists
  only because surface syntax does not carry this; the environment does.

Usage:
  lake exe comparator_facts <Module> <declaration>

The declaration may be given in full or by any whole suffix, the same rule
the Python generator uses.
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
    let rangeJson := match ranges with
      | some r => Json.mkObj [
          ("startLine", toJson r.range.pos.line),
          ("startColumn", toJson r.range.pos.column),
          ("endLine", toJson r.range.endPos.line),
          ("endColumn", toJson r.range.endPos.column)]
      | none => Json.null
    let payload := Json.mkObj [
      ("declaration", toJson decl),
      ("name", toJson name.toString),
      ("range", rangeJson),
      ("binders", toJson binders.toList),
      ("answerTypes", toJson answerTypes.toList)]
    IO.println payload.pretty
    return 0
