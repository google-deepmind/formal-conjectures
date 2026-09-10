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
import FormalConjecturesTest.ForMathlib.Computability.PromiseApproximation
import Lean.Util.CollectAxioms

/-!
# Transitive axiom audit for approximation and promise problems

Audit all declarations in the seven supporting modules and test module,
including generated declarations and instances. Research statements are not imported.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `FormalConjecturesForMathlib.Computability.BooleanSatisfiability,
    `FormalConjecturesForMathlib.Computability.MatrixGraphProblems,
    `FormalConjecturesForMathlib.Computability.PromiseProblems,
    `FormalConjecturesForMathlib.Computability.LabelCover,
    `FormalConjecturesForMathlib.Computability.PromiseGraph,
    `FormalConjecturesForMathlib.Computability.SmallSetExpansion,
    `FormalConjecturesForMathlib.Computability.GapSatisfiability,
    `FormalConjecturesTest.ForMathlib.Computability.PromiseApproximation]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut total : Nat := 0
  for mod in modules do
    let mut checked : Nat := 0
    let mut used : Array Name := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx]! == mod then
          let axioms ← collectAxioms name
          for ax in axioms do
            unless allowed.contains ax do
              throwError m!"{name} depends on unexpected axiom {ax}"
            unless used.contains ax do
              used := used.push ax
          checked := checked + 1
    if checked == 0 then
      throwError m!"Audit found no declarations for {mod}"
    total := total + checked
    logInfo m!"{mod}: checked {checked} declarations; axioms {used.qsort Name.lt}"
  logInfo m!"Passed: {total} declarations audited transitively."
