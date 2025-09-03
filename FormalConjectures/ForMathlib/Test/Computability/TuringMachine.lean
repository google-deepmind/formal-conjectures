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

import FormalConjectures.ForMathlib.Computability.TuringMachine.Notation
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

example : turing_machine% "------" = fun _ _ => none := by
  aesop

example : turing_machine% "1RA0LB_0LA---" = fun a b =>
    match a, b with
    | .A, 0 => some (some .A, Stmt.write 1 .right)
    | .A, 1 => some (some .B, Stmt.write 0 .left)
    | .B, 0 => some (some .A, Stmt.write 0 .left)
    | .B, 1 => none := by
  aesop

example : turing_machine% "1RZ0LZ_------" = fun a b =>
    match a, b with
    | .A, 0 => some (none, Stmt.write 1 .right)
    | .A, 1 => some (none, Stmt.write 0 .left)
    | .B, 0 => none
    | .B, 1 => none :=
  rfl

example : turing_machine% "1RZ0LZ2LZ_---------" = fun a b =>
    match a, b with
      | .A, 0 => some (none, Stmt.write 1 .right)
      | .A, 1 => some (none, Stmt.write 0 .left)
      | .A, 2 => some (none, Stmt.write 2 .left)
      | .B, 0 => none
      | .B, 1 => none
      | .B, 2 => none :=
  rfl

/-- error: Invalid write instruction: A is not a numeral. -/
#guard_msgs in
#check turing_machine% "---ALZ_------"

/-- error: Invalid direction A. -/
#guard_msgs in
#check turing_machine% "---0AZ_------"

/--
info: fun a b ↦
  match a, b with
  | State2.A, 0 => none
  | State2.A, 1 => some (none, { symbol := 0, dir := Dir.left })
  | State2.B, 0 => none
  | State2.B, 1 => none : State2 → Fin 2 → Option (Option State2 × Stmt (Fin 2))
-/
#guard_msgs in
#check turing_machine% "---0LZ_------"

/-- error: All portions of the string separated by `_` should have the same length -/
#guard_msgs in
#check turing_machine% "---0LZ_-----"

instance : haltsAfterOne.IsHalting := by
  rw [isHalting_iff_exists_haltsAt]
  -- halts after one step
  exact ⟨1, by aesop⟩

theorem haltsAfterOne_haltingNumber : haltsAfterOne.haltingNumber = 1 := by
  apply haltingNumber_def
  · use { q := some Λ.T, tape := ⟨Γ.A, Quotient.mk'' [Γ.A], default⟩}
    rfl
  · rfl
