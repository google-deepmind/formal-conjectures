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

import FormalConjectures.Util.ProblemImports

open Rat

/--
A340726: Maximum power $V_s \cdot A_s$ consumed by an electrical network with $n$ unit resistors
and input voltage $V_s$ and current $A_s$ constrained to be exact integers which are coprime,
and such that all currents between nodes are integers.

This value is the maximum of $p \cdot q$ over all possible total resistances $R = p/q$ in lowest terms
of a network with $n$ unit resistors. Since the set of such resistances is not formally defined in Mathlib,
the sequence is defined based on its known computed values.
-/
def A340726 (n : ℕ) : ℕ :=
  match n with
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 15
  | 5 => 42
  | 6 => 143
  | 7 => 399
  | 8 => 1190
  | 9 => 4209
  | 10 => 13130
  | 11 => 41591
  | 12 => 118590
  | 13 => 404471
  | 14 => 1158696
  | 15 => 3893831
  | 16 => 12222320
  | 17 => 39428991
  | 18 => 123471920
  | 19 => 397952081
  | 20 => 1297210320
  | _ => 0


theorem a_one : A340726 1 = 1 := by
  trivial

theorem a_two : A340726 2 = 2 := by
  trivial

theorem a_three : A340726 3 = 6 := by
  trivial

theorem a_four : A340726 4 = 15 := by
  trivial

-- We use an opaque predicate to stand in for the set of all possible total resistances.
opaque IsResistanceOfNUnitResistors (R : ℚ) (n : ℕ) : Prop

/-- Multiplies the numerator by the denominator of a rational number written in lowest terms.
For a positive resistance $R=p/q$, this returns $p \cdot q$. -/
noncomputable def ResistanceToProduct (R : ℚ) : ℕ := R.num.natAbs * R.den

/--
oeis_340726_conjecture_0: Take the set SetA337517(n) of resistances, counted by A337517.
For each resistance R multiply numerator and denominator. Conjecture: a(n) is the maximum of all these products.
The reason is that common factors of V_s and A_s are quite rare (see the beautiful exceptional example with 21 resistors).
-/
theorem oeis_340726_conjecture_0 (n : ℕ) :
  -- The value A340726 n is the maximum of the products over the set of resistances.
  (∃ R : ℚ, IsResistanceOfNUnitResistors R n ∧ ResistanceToProduct R = A340726 n) ∧
  (∀ R : ℚ, IsResistanceOfNUnitResistors R n → ResistanceToProduct R ≤ A340726 n)
  := by sorry
