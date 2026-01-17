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
# Ben Green's Open Problem 70

*Reference:* [Ben Green's Open Problem 70](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.9 Problem 70)
-/

namespace Green70

/-- Three or more points are collinear. -/
def Collinear (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ (a b c : ℝ), (a, b) ≠ (0, 0) ∧ ∀ p ∈ S, a * p.1 + b * p.2 = c

/-- Two points are mutually visible in a set if the open line segment between them contains
no other point from the set. -/
def MutuallyVisible (A : Finset (ℝ × ℝ)) (x y : ℝ × ℝ) : Prop :=
  x ∈ A ∧ y ∈ A ∧ x ≠ y ∧
  ∀ z ∈ A, z ≠ x → z ≠ y →
    ¬∃ (t : ℝ), 0 < t ∧ t < 1 ∧ z = (1 - t) • x + t • y

/-- A set of points is pairwise mutually visible. -/
def PairwiseMutuallyVisible (A : Finset (ℝ × ℝ)) (S : Finset (ℝ × ℝ)) : Prop :=
  S ⊆ A ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → MutuallyVisible A x y

/--
Fix integers $k, l$. Is it true that, given a set of $n \geq n_0(k, l)$ points in $\mathbb{R}^2$,
either some $k$ of them lie on a line, or some $l$ of them are 'mutually visible', that is to
say the line segment joining them contains no other point from the set?
-/
@[category research open, AMS 5 52]
theorem green_70 :
    answer(sorry) ↔ ∀ k l : ℕ, ∃ n₀ : ℕ,
      ∀ (A : Finset (ℝ × ℝ)), A.card ≥ n₀ →
        (∃ (S : Finset (ℝ × ℝ)), S ⊆ A ∧ S.card = k ∧ Collinear S) ∨
        (∃ (S : Finset (ℝ × ℝ)), S.card = l ∧ PairwiseMutuallyVisible A S) := by
  sorry

end Green70
