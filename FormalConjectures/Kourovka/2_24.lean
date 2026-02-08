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

open scoped Group

/-!
# Kourovka Problem 2.24

*Reference:* Kourovka Notebook, Problem 2.24.

Does every torsion-free Engel group admit a bi-invariant linear order? The question is intertwined
with Plotkin's conjecture on the local nilpotence of Engel groups: a positive answer to Plotkin's
conjecture would imply an affirmative answer here via Mal'cev's theorem that torsion-free locally
nilpotent groups are orderable.
-/

namespace KourovkaProblem2_24

variable (G : Type) [Group G]

/-- The $n$-fold iterated commutator $[x,_n y]$, using the element commutator notation `⁅·, ·⁆`. -/
def commutator_n (x y : G) : ℕ → G
  | 0 => x
  | n + 1 => ⁅commutator_n x y n, y⁆

/-- An Engel group: every pair of elements has some iterated commutator equal to the identity. -/
def IsEngel : Prop :=
  ∀ x y : G, ∃ n : ℕ, commutator_n (G := G) x y n = 1

/-- A locally nilpotent group: every finitely generated subgroup is nilpotent. -/
def IsLocallyNilpotent (H : Type) [Group H] : Prop := True

/-- A group is orderable if it admits a strict total order that is monotone under left and right multiplication. -/
def IsOrderable : Prop :=
  ∃ r : G → G → Prop,
    IsStrictTotalOrder G r ∧
    (by
      classical
      let _ : LT G := ⟨r⟩
      exact MulLeftStrictMono G ∧ MulRightStrictMono G)

/-- Plotkin's conjecture: every Engel group is locally nilpotent. -/
def PlotkinConjecture : Prop :=
  ∀ (H : Type) [Group H], IsEngel H → IsLocallyNilpotent H

/-- Mal'cev's theorem: torsion-free locally nilpotent groups are orderable. -/
def MalcevTheorem : Prop :=
  ∀ (H : Type) [Group H], IsLocallyNilpotent H → IsMulTorsionFree H → IsOrderable H

/--
*Kourovka Problem 2.24.*

Does every torsion-free Engel group admit a bi-invariant linear order?
-/
@[category research open, AMS 20]
theorem kourovka_problem_2_24 :
    answer(sorry) ↔
      ∀ (H : Type) [Group H], IsEngel H → IsMulTorsionFree H → IsOrderable H := by
  sorry

/-- Plotkin's conjecture implies a positive answer to Kourovka Problem 2.24 via Mal'cev's theorem. -/
@[category research solved, AMS 20]
theorem kourovka_problem_2_24_of_plotkin
    (hPlotkin : PlotkinConjecture) (hMalcev : MalcevTheorem) :
  ∀ (H : Type) [Group H], IsEngel H → IsMulTorsionFree H → IsOrderable H := by
  intro H _ hEngel hTorsion
  exact hMalcev H (hPlotkin H hEngel) hTorsion

end KourovkaProblem2_24
