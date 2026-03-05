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

/-!
# Erdős Problem 1124

Can a square and a circle of the same area be decomposed into a finite number of
congruent parts? (Tarski's circle-squaring problem.)

*Reference:* [erdosproblems.com/1124](https://www.erdosproblems.com/1124)

[La90b] Laczkovich, M., _Equidecomposability and discrepancy; a solution of Tarski's
circle-squaring problem_. J. Reine Angew. Math. **404** (1990), 77-117.
-/

namespace Erdos1124

/-- The unit square $[0,1]^2$ in $\mathbb{R}^2$. -/
noncomputable def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

/--
Erdős Problem 1124 (Tarski's circle-squaring problem, proved):

Can a square and a circle of the same area be decomposed into a finite number
of congruent parts?

A problem of Tarski, which Erdős described as 'a very beautiful problem...if it
were my problem I would offer \$1000 for it'.

Laczkovich [La90b] proved that this is possible using translations only.

Formally: the unit square and the closed disk of radius $1/\sqrt{\pi}$ (both having area $1$)
can be partitioned into finitely many pieces such that corresponding pieces are
congruent (related by isometries of $\mathbb{R}^2$).
-/
@[category research solved, AMS 28 51]
theorem erdos_1124 : answer(True) ↔
    ∃ (n : ℕ),
    ∃ (pieces_sq pieces_disk : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      -- The pieces partition the unit square
      (⋃ i, pieces_sq i) = unitSquare ∧
      (∀ i j, i ≠ j → Disjoint (pieces_sq i) (pieces_sq j)) ∧
      -- The pieces partition the closed disk of radius 1/√π (same area as unit square)
      (⋃ i, pieces_disk i) =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / Real.sqrt Real.pi) ∧
      (∀ i j, i ≠ j → Disjoint (pieces_disk i) (pieces_disk j)) ∧
      -- Corresponding pieces are congruent (related by an isometry)
      (∀ i, ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
        Isometry f ∧ f '' (pieces_sq i) = pieces_disk i) := by
  sorry

end Erdos1124
