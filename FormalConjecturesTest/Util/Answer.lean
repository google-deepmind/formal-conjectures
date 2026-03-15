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
import FormalConjectures.Util.Answer

section WithAuxiliary

open Google

open Lean Elab Meta

set_option google.answer "with_auxiliary"

open Lean Elab Meta

theorem foo : answer(True) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `foo._answer | throwError "here"
  trivial

theorem bar : 1 = answer(sorry) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = 1 = bar._answer
  sorry

theorem bar_symm : answer(sorry) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm._answer = 1
  sorry

theorem i_have_some_universes.{u, v} (X : Type u) (Y : Type v) : (X × Y) = answer(sorry) := by
  guard_target = (X × Y : Type (max u v)) = i_have_some_universes._answer.{u, v}
  sorry

end WithAuxiliary

section AlwaysTrue

set_option google.answer "always_true"

theorem this_works : (answer(sorry) : Prop) := by
  trivial

end AlwaysTrue
