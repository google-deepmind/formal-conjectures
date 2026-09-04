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
import ComparatorFacts.Binders
import ComparatorFacts.Extract

/-!
The executable over `ComparatorFacts/`: the elaborator-side facts `comparator/adapter/fc_leaneval_importer.py` would otherwise
get by reading Lean with regular expressions.

Given a module and a declaration name, this prints JSON with what the
elaborated environment knows exactly and the text layer can only guess:

- the declaration's source range, for slicing its original text;
- its declaration-header binders, with names and explicitness, for the
  Solution adapter;
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

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
    runWithImports #[`Mathlib] do binderBoundarySelfTest (← getEnv)
  | ["--batch"] =>
    -- One `{"module": M, "declaration": D}` object per stdin line, one
    -- environment for all of them: the Mathlib import dominates a run, and
    -- `resolveIn` filters by module, so a shared environment answers each
    -- pair exactly as a per-module import does. JSON lines rather than
    -- space-delimited fields, because a guillemet name may contain anything.
    -- One JSON object per line out, in input order.
    let stdin ← IO.getStdin
    let lines := (← stdin.readToEnd).splitOn "\n" |>.filter (· ≠ "")
    let pairs ← lines.mapM fun line => do
      match Json.parse line with
      | .error msg => throw <| IO.userError s!"malformed batch line: {line} ({msg})"
      | .ok json =>
        match json.getObjValAs? String "module", json.getObjValAs? String "declaration" with
        | .ok modName, .ok declName => pure (modName, declName)
        | _, _ => throw <| IO.userError s!"malformed batch line: {line}"
    let modules := pairs.foldl (init := #[]) fun acc (m, _) =>
      if acc.contains m.toName then acc else acc.push m.toName
    -- The heartbeat budget is shared by the whole action, so it scales with
    -- the batch; each pair keeps the single-run allowance.
    runWithImports modules
      (heartbeats := pairs.length * heartbeatsPerDeclaration) do
      let env ← getEnv
      for (modName, declName) in pairs do
        let tagged (rest : List (String × Json)) := Json.mkObj <|
          [("module", Json.str modName), ("declaration", Json.str declName)] ++ rest
        match resolveIn env modName.toName declName with
        | .error msg => IO.println (tagged [("error", Json.str msg)]).compress
        | .ok n =>
          try
            let payload ← factsPayload env modName.toName n declName
            IO.println (tagged [("facts", payload)]).compress
          catch e =>
            IO.println (tagged [("error", Json.str (← e.toMessageData.toString))]).compress
      return 0
  | [modName, declName] =>
    runWithImports #[modName.toName] do
      let env ← getEnv
      match resolveIn env modName.toName declName with
      | .error msg => IO.eprintln msg; return 1
      | .ok n =>
        IO.println (← factsPayload env modName.toName n declName).pretty
        return 0
  | _ =>
    IO.eprintln "usage: comparator_facts <Module> <declaration> | --batch | --self-test"
    return 1
where
  factsPayload (env : Environment) (modName name : Name) (decl : String) : MetaM Json := do
    let some info := env.find? name | throwError "{name} vanished from the environment"
    let some ranges ← findDeclarationRanges? name
      | throwError "{name} has no source range"
    -- The statement's sorries are `answer(sorry)` slots; a proof's sorry is
    -- not in the *type*, so everything found here is a slot.
    -- `findAnswerExprs` is the repository's own detection: it reads the
    -- annotation the `answer` elaborator leaves, rather than guessing from
    -- `sorryAx` applications.
    let answerTypes ← forallTelescope info.type fun xs body => do
      -- The slots live anywhere in the statement: a hypothesis binder
      -- `(h : c = answer(sorry))` carries one just as the conclusion can.
      -- Binder types come from the telescope's local declarations, so the
      -- expressions are closed in the local context and inferType works.
      let mut found := #[]
      for x in xs do
        found := found ++ Google.findAnswerExprs (← x.fvarId!.getDecl).type
      found := found ++ Google.findAnswerExprs body
      found.mapM fun a => do pure (toString (← ppExpr (← inferType a)))
    let sourceResult ← declarationSource modName ranges
    let declarationText ← match sourceResult with
      | .ok source => pure source
      | .error message => throwError message
    let (header, resultType) ← match declarationText.headerAndResult with
      | .ok pieces => pure pieces
      | .error message => throwError message
    let command ← match Parser.runParserCategory env `command header with
      | .ok command => pure command
      | .error message =>
        throwError "could not recover declaration parameters for {name}: {message}"
    let conclusion ← match conclusionBinders env resultType with
      | .ok binders => pure binders
      | .error message =>
        throwError "could not recover conclusion parameters for {name}: {message}"
    let binders ← forallTelescope info.type fun xs _ => do
      let declarations ← xs.mapM fun x => x.fvarId!.getDecl
      let arity ← match declarationParameterBoundary command conclusion declarations with
        | .ok arity => pure arity
        | .error message =>
          throwError "could not align declaration parameters for {name}: {message}"
      (declarations.extract 0 arity).mapM fun d =>
        pure (binderJson d.userName d.binderInfo)
    let rangeJson := rangeToJson (some ranges)
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
    return payload
  rangeToJson (ranges : Option DeclarationRanges) : Json :=
    match ranges with
    | some r => Json.mkObj [
        ("startLine", toJson r.range.pos.line),
        ("startColumn", toJson r.range.pos.column),
        ("endLine", toJson r.range.endPos.line),
        ("endColumn", toJson r.range.endPos.column)]
    | none => Json.null
