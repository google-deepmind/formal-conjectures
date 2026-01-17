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
# Ben Green's Open Problem 68

*Reference:* [Ben Green's Open Problem 68](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.9 Problem 68)
-/

open Filter

namespace Green68

variable (p : ℕ) [Fact p.Prime]

/-- A line in $\mathbb{F}_p^2$ is the set of points satisfying $ax + by = c$ for some $a, b, c$
    with $(a, b) \neq (0, 0)$. -/
def Line (a b c : ZMod p) (hab : (a, b) ≠ (0, 0)) : Set (ZMod p × ZMod p) :=
  {pt | a * pt.1 + b * pt.2 = c}

/-- A set meets every line in at most $k$ points. -/
def MeetsLinesIn (A : Set (ZMod p × ZMod p)) (k : ℕ) : Prop :=
  ∀ a b c : ZMod p, ∀ hab : (a, b) ≠ (0, 0),
    (A ∩ Line p a b c hab).ncard ≤ k

/-- A cubic curve in $\mathbb{F}_p^2$ is the zero set of a degree-3 polynomial. -/
def OnCubicCurve (A : Set (ZMod p × ZMod p)) : Prop :=
  ∃ (f : MvPolynomial (Fin 2) (ZMod p)), f.totalDegree ≤ 3 ∧ f ≠ 0 ∧
    ∀ pt ∈ A, MvPolynomial.eval ![pt.1, pt.2] f = 0

/--
Suppose that $A \subset \mathbb{F}_p^2$ is a set meeting every line in at most 2 points.
Is it true that all except $o(p)$ points of $A$ lie on a cubic curve?
-/
@[category research open, AMS 5 11 14]
theorem green_68 :
    answer(sorry) ↔ ∀ᶠ p in atTop, ∀ [Fact (Nat.Prime p)],
      ∀ (A : Finset (ZMod p × ZMod p)),
        MeetsLinesIn p A.toSet 2 →
        ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
        ∃ (B : Finset (ZMod p × ZMod p)), B ⊆ A ∧ OnCubicCurve p B.toSet ∧
          (A.card - B.card : ℝ) ≤ o p * p := by
  sorry

end Green68
