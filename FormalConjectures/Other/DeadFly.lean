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

public import FormalConjecturesUtil

/-!
# Conway's Dead Fly Problem

Conway's problem asks whether a set meeting every convex region
of area one in the plane must contain distinct points
at arbitrarily small distances.

This is the nonexistence formulation of the planar Boshernitzan-Conway
problem: it asks whether a uniformly discrete Danzer set can be ruled out.
Uniform discreteness means that the distances between distinct points
have a common strictly positive lower bound.

Adiceam discusses the corresponding existence question in Section 2.2,
Problem 9, of his survey. The uniform discreteness condition is stronger
than the finite density condition in Danzer's original problem.

## References

* [Conway's problem list, Problem 4](https://oeis.org/A195264/a195264_4.pdf).
* F. Adiceam,
  [Around the Danzer Problem and the Construction of Dense Forests](https://arxiv.org/abs/2010.06756),
  Section 2.2, Problem 9. Published in L'Enseignement Mathematique 68 (2022), 25-60.
* Y. Solomon and B. Weiss,
  [Dense forests and Danzer sets](https://doi.org/10.24033/asens.2303),
  Annales scientifiques de l'Ecole Normale Superieure 49 (2016), 1053-1074.
-/

@[expose] public section

namespace DeadFly

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The set `S` meets every convex region of area one. -/
def MeetsEveryConvexRegion (S : Set Plane) : Prop :=
  ∀ C : Set Plane,
    Convex ℝ C ∧ MeasureTheory.volume C = 1 → (S ∩ C).Nonempty

/-- The set `S` contains pairs of distinct points at arbitrarily small distances.

Every entourage contains a pair of distinct points of `S`.

Equivalent metric formulation:

    ∀ ε : ℝ, ε > 0 → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ dist x y < ε
-/
def ArbitrarilyClosePoints (S : Set Plane) : Prop :=
  Filter.Frequently
    (fun p : Plane × Plane =>
      p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2)
    (uniformity Plane)

/-- If a set of points in the plane contains one point in each convex region of area $1$, then
must it have pairs of points at arbitrarily small distances? -/
@[category research open, question, AMS 52]
lemma dead_fly_problem :
    ∀ S : Set Plane, MeetsEveryConvexRegion S → ArbitrarilyClosePoints S := by
  sorry

end DeadFly
