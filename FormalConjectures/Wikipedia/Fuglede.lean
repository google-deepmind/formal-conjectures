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
# Fuglede's conjecture in dimensions 1 and 2

*References:*
- [Fuglede's conjecture](https://en.wikipedia.org/wiki/Fuglede%27s_conjecture)
- [Zh26] [Zhang, Tao, *Both directions of Fuglede's conjecture fail in dimension two*,
  arXiv:2607.15632 (2026)](https://arxiv.org/abs/2607.15632)
-/

namespace Fuglede

open MeasureTheory

/--
**Fuglede's conjecture** in dimension `n`: A bounded subset of ℝ^n with positive Lebesgue measure is spectral iff it tiles ℝ^n by translation.
-/
def FugledeConjectureFor (n : ℕ) : Prop :=
  ∀ Ω : Set (Fin n → ℝ),
    Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
      (isSpectral Ω ↔ tilesByTranslation Ω)

/--
**Fuglede's conjecture** in one dimension: A bounded subset of ℝ with positive Lebesgue measure is spectral iff it tiles ℝ by translation.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_1 :
    answer(sorry) ↔ FugledeConjectureFor 1 := by
  sorry

/--
**Fuglede's conjecture** in two dimensions: A bounded subset of ℝ^2 with positive Lebesgue measure is spectral iff it tiles ℝ^2 by translation.

[Zh26], a July 2026 preprint, announces a negative answer in both directions, from two
explicit $60$-point subsets of $\mathbb{Z}_{60} \times \mathbb{Z}_{12}$ lifted to finite
unions of unit squares in $\mathbb{R}^2$. It is not yet published.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_2 :
    answer(sorry) ↔ FugledeConjectureFor 2 := by
  sorry

/--
**Fuglede's conjecture** in three or higher dimensions has been disproven.
(Note that counterexamples in lower dimensions would also disprove the conjecture in higher dimensions.)
-/
@[category research solved, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_3_or_higher :
    answer(False) ↔ ∀ n : ℕ, 3 ≤ n → FugledeConjectureFor n := by
  sorry

end Fuglede
