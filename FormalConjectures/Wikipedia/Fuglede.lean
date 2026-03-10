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
import FormalConjecturesForMathlib.Analysis.Fourier.Fuglede

/-!
# Fuglede's conjecture in dimensions 1 and 2

*References:*
- [Fuglede's conjecture](https://en.wikipedia.org/wiki/Fuglede%27s_conjecture)
-/

namespace Fuglede

open Real Set Complex MeasureTheory
open scoped InnerProductSpace

/--
**Fuglede's conjecture** in one dimension: A bounded subset of ℝ with positive Lebesgue measure is spectral iff it tiles ℝ by translation.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_1 :
    answer(sorry) ↔
      ∀ Ω : Set (Fin 1 → ℝ),
        Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
          (isSpectral Ω ↔ tilesByTranslation Ω) := by
  sorry

/--
**Fuglede's conjecture** in two dimensions: A bounded subset of ℝ^2 with positive Lebesgue measure is spectral iff it tiles ℝ^2 by translation.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_2 :
    answer(sorry) ↔
      ∀ Ω : Set (Fin 2 → ℝ),
        Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
          (isSpectral Ω ↔ tilesByTranslation Ω) := by
  sorry

/--
**Fuglede's conjecture** in three or higher dimensions has been disproven.
(Note that counterexamples in lower dimensions would also disprove the conjecture in higher dimensions.)
-/
@[category research solved, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_3_or_higher :
    answer(False) ↔
      ∀ Ω : Set (Fin 3 → ℝ),
        Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
          (isSpectral Ω ↔ tilesByTranslation Ω) := by
  sorry

end Fuglede
