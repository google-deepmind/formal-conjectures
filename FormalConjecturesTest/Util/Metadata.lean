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

public import FormalConjecturesTest.Util.MetadataFixture
public meta import FormalConjecturesUtil.ProblemMetadata

meta section

open Lean FormalConjectures.Metadata

private unsafe def checkMetadata : CoreM Unit := do
  let problems ← extractProblems #[`FormalConjecturesTest.Util.MetadataFixture]
  unless problems.length == 3 do
    throwError m!"expected three named problems: {problems.map (·.theorem)}"
  let some conditional := problems.find? (·.theorem == "MetadataFixture.«quoted name»")
    | throwError "quoted declaration missing"
  unless conditional.formalProofs.map (·.conditions) == [["MetadataFixture.assumption"]] &&
      conditional.hasSorryFreeProof do
    throwError "conditional proof metadata changed"
  let some problem := problems.find? (·.theorem == "MetadataFixture.problem")
    | throwError "primary declaration missing"
  unless problem.answerKinds == ["Prop"] && !problem.hasSorryFreeProof do
    throwError "proposition answer hole lost"
  let some variant := problems.find? (·.theorem == "MetadataFixture.problem.variant")
    | throwError "variant missing"
  unless variant.answerKinds == ["non-Prop"] do
    throwError "value answer hole lost"
  let again ← extractProblems #[`FormalConjecturesTest.Util.MetadataFixture]
  unless (problems.map (·.toFilteredJson)) == (again.map (·.toFilteredJson)) do
    throwError "metadata extraction is not deterministic"
  if ((problem.toFilteredJson).getObjValAs? (List Json) "formalProofs").toOption.isSome then
    throwError "empty formalProofs must remain omitted in schema 2"

private unsafe def testMetadata : IO Unit := do
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let env ← importModules #[{ module := `FormalConjecturesTest.Util.MetadataFixture }]
    {} (trustLevel := 1024) (loadExts := true)
  let _ ← Core.CoreM.toIO checkMetadata { fileName := "", fileMap := default } { env := env }

#eval testMetadata
