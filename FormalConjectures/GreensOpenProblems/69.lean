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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 69

*Reference:* [Ben Green's Open Problem 69](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.9 Problem 69)
-/

namespace Green69

/-- Three points in the plane are collinear. -/
def Collinear (x y z : ℝ × ℝ) : Prop :=
  ∃ (a b c : ℝ), (a, b) ≠ (0, 0) ∧ a * x.1 + b * x.2 = c ∧ a * y.1 + b * y.2 = c ∧ a * z.1 + b * z.2 = c

/-- The line through two distinct points contains a third point from the set. -/
def HasThirdPoint (A : Finset (ℝ × ℝ)) (x y : ℝ × ℝ) : Prop :=
  x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ ∃ z ∈ A, z ≠ x ∧ z ≠ y ∧ Collinear x y z

/-- A set of points lies on a cubic curve. -/
def OnCubicCurve (A : Set (ℝ × ℝ)) : Prop :=
  ∃ (f : MvPolynomial (Fin 2) ℝ), f.totalDegree ≤ 3 ∧ f ≠ 0 ∧
    ∀ pt ∈ A, MvPolynomial.eval ![pt.1, pt.2] f = 0

/--
Fix a number $k$. Let $A \subset \mathbb{R}^2$ be a set of $n$ points, with no more than $k$ on
any line. Suppose that, for at least $\delta n^2$ pairs of points $(x, y) \in A \times A$, the
line $xy$ contains a third point of $A$. Is there some cubic curve containing at least $cn$
points of $A$, for some $c = c(k, \delta) > 0$?
-/
@[category research open, AMS 5 14 52]
theorem green_69 :
    answer(sorry) ↔ ∀ k : ℕ, ∀ δ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ n : ℕ, ∀ (A : Finset (ℝ × ℝ)),
        A.card = n →
        (∀ (L : Set (ℝ × ℝ)), (∃ a b d : ℝ, (a, b) ≠ (0, 0) ∧
          L = {p | a * p.1 + b * p.2 = d}) → (A.toSet ∩ L).ncard ≤ k) →
        (({p : (ℝ × ℝ) × (ℝ × ℝ) | HasThirdPoint A p.1 p.2}.ncard : ℝ) ≥ δ * n ^ 2) →
        ∃ (B : Finset (ℝ × ℝ)), B ⊆ A ∧ OnCubicCurve B.toSet ∧ (B.card : ℝ) ≥ c * n := by
  sorry

end Green69
