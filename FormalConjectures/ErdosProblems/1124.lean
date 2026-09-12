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

import FormalConjecturesUtil

/-!
# Erdős Problem 1124

*Reference:* [erdosproblems.com/1124](https://www.erdosproblems.com/1124)
-/

open Set Metric

namespace Erdos1124

/-- Two subsets of the plane are congruent if there is an isometry of $\mathbb{R}^2$ carrying one
onto the other. -/
def Congruent (A B : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2), f '' A = B

/-- A finite decomposition of `A` and `B` into pairwise congruent pieces. -/
def FiniteCongruentDecomposition (A B : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ n : ℕ, ∃ P Q : Fin n → Set (EuclideanSpace ℝ (Fin 2)),
    (⋃ i, P i) = A ∧ (⋃ i, Q i) = B ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      ∀ i, Congruent (P i) (Q i)

/-- The closed unit square $[0,1]^2$. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  { x | ∀ i, x i ∈ Icc (0 : ℝ) 1 }

/-- The closed disc of area $1$ (radius $1/\sqrt{\pi}$). -/
noncomputable def areaOneDisc : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall 0 (1 / Real.sqrt Real.pi)

/--
Can a square and a circle of the same area be decomposed into a finite number of congruent parts?
-/
@[category research open, AMS 51 52]
theorem erdos_1124 :
    answer(sorry) ↔ FiniteCongruentDecomposition unitSquare areaOneDisc := by
  sorry

end Erdos1124
