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
# Gap conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth#The_gap_conjecture)
- [On the Gap Conjecture concerning group growth](https://arxiv.org/pdf/1202.6044) by
  *Rostislav Grigorchuk*
-/

namespace GapConjecture

open Filter GromovPolynomialGrowth

/--
If a finitely generated group has superpolynomial growth, then with respect to any finite
generating set its growth function is at least $e^{\sqrt n}$ in Grigorchuk's preorder on
growth functions, where the comparison is witnessed by linearly rescaling the radius.
-/
@[category research open, AMS 20]
theorem gap_conjecture :
    ∀ (G : Type) [Group G] (S : Set G), S.Finite → Subgroup.closure S = ⊤ →
      HasSuperPolynomialGrowth G →
      ∃ C : ℕ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop, Real.exp (Real.sqrt (n : ℝ)) ≤
          (GrowthFunction S (C * n) : ℝ) := by
  sorry

end GapConjecture
