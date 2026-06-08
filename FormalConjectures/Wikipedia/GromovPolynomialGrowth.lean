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

*Reference:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth)
-/

/-
Note: this was obtained in work with Kasia Jankiewicz and Catherine Pfaff, and using
Claude 4.0 Sonnet: https://claude.ai/share/918bb269-bd28-4c09-b84e-cab579c836e8
-/

namespace GromovPolynomialGrowth

open Filter

variable {G : Type*} [Group G]

/-- Infinite groups do not satisfy polynomial growth over `ℕ` for any degree `d` because when
`d = 0` this reduces to the unbounded nature of `growthFunction` while `n = 0` works when `d ≠ 0`.
Thus a finitely-generated infinite nilpotent group would be a counter-example to
Gromov's theorem when quantifying over all of `ℕ`, and so `n = 0` should be excluded. -/
@[category test, AMS 20]
theorem growthFunction_not_polynomial_of_infinite [Infinite G] {S : Set G} (hS : S.Finite)
    (h : Subgroup.closure S = ⊤) {C : ℝ} (d : ℕ) :
    ∃ (n : ℕ), C * n ^ d < GrowthFunction S n := by
  by_cases hd : d = 0
  · obtain ⟨n, _, hn⟩ := exists_lt_of_tendsto_atTop (tendsto_atTop_growthFunction_of_infinite hS h)
      0 ⌈C⌉₊
    use n
    grw [Nat.le_ceil C]
    simpa [hd] using mod_cast hn
  · exact ⟨0, by simp [hd, growthFunction_zero]⟩

variable (G)

/-- **Gromov's Polynomial Growth Theorem** : A finitely generated group has
    polynomial growth if and only if it is virtually nilpotent. -/
@[category research solved, AMS 20]
theorem GromovPolynomialGrowthTheorem [Group.FG G] :
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G := by
  sorry

end GromovPolynomialGrowth
