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

import FormalConjectures.ForMathlib.Computability.TuringMachine
import Mathlib.Tactic.DeriveFintype

--sanity checks for the definition of halting added in `ForMathlib`.
--These should be easy to prove

open Turing BusyBeaver

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

instance : alwaysHaltingMachine.IsHalting where
  halts := by
    simp_rw (config := { singlePass := true })
      [BusyBeaver.eval, Turing.eval, Part.map_Dom, step, alwaysHaltingMachine, Option.map_none',
      Part.dom_iff_mem, PFun.mem_fix_iff, Part.mem_some_iff]
    use default
    aesop

-- TODO(Paul-Lez): finish proving this
instance : haltsAfterOne.IsHalting  where
  halts := by
    sorry
