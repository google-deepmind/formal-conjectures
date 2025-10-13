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

import FormalConjectures.ForMathlib.Computability.TuringMachine.BusyBeavers
import Mathlib.Tactic.DeriveFintype

--sanity checks for the definition of halting added in `ForMathlib`.
--These should be easy to prove

open Turing BusyBeaver Machine

inductive Γ where
  | A
  | B
deriving Inhabited, Fintype

inductive Λ where
  | S
  | T
deriving Inhabited, Fintype

def alwaysHaltingMachine : Machine Γ Λ := fun _ _ =>
  none

def haltsAfterOne : Machine Γ Λ := fun l _ =>
match l with
| --If the state is `S`, change state to `T` and move head to the right
  .S => some (Λ.T, Stmt.write default Dir.right)
| --If the state is already `T` then halt
  .T => none

instance : alwaysHaltingMachine.IsHalting := by
  rw [isHalting_iff_exists_haltsAt]
  -- halts after zero steps
  exact ⟨0, by aesop⟩

instance : haltsAfterOne.IsHalting := by
  rw [isHalting_iff_exists_haltsAt]
  -- halts after one step
  exact ⟨1, by aesop⟩

theorem haltsAfterOne_haltingNumber : haltsAfterOne.haltingNumber = 1 := by
  apply haltingNumber_def
  · use { q := some Λ.T, tape := ⟨Γ.A, Quotient.mk'' [Γ.A], default⟩}
    rfl
  · rfl
