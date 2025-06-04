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
# Gromov's theorem on groups of polynomial growth

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth)
-/

/-
Note: this was obtained in work with Kasia Jankiewicz and Catherine Pfaff, and using
Claude 4.0 Sonnet: https://claude.ai/share/918bb269-bd28-4c09-b84e-cab579c836e8
-/

/-- The `CayleyBall` is the ball of radius `n` in the Cayley graph of a group `G` with generating
    set `S`. -/
def CayleyBall {G : Type*} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

/-- The `GrowthFunction` of a group `G` with respect to a set `S` counts the number
    of group elements that can be reached by words of length at most `n` in `S`. -/
noncomputable def GrowthFunction {G : Type*} [Group G] (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

/-- A group `HasPolynomialGrowth` if there exists a finite generating set such that
    the growth function is bounded above by a polynomial. -/
def HasPolynomialGrowth (G : Type*) [Group G] : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n : ℕ, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

/-- A group `IsVirtuallyNilpotent` if it contains a nilpotent subgroup of finite index. -/
def IsVirtuallyNilpotent (G : Type*) [Group G] : Prop :=
  ∃ (H : Subgroup G), Group.IsNilpotent H ∧ H.FiniteIndex

/-- **Gromov's Polynomial Growth Theorem** : A finitely generated group has
    polynomial growth if and only if it is virtually nilpotent. -/
@[category research solved, AMS 20]
theorem GromovPolynomialGrowthTheorem (G : Type*) [Group G] [Group.FG G] :
    HasPolynomialGrowth G ↔ IsVirtuallyNilpotent G := by
  sorry
