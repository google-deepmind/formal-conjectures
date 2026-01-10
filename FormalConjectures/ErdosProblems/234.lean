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
# Erdős Problem 234

*Reference:* [erdosproblems.com/234](https://www.erdosproblems.com/234)
-/

open Set NNReal

namespace Erdos234

/--
Is it true that for all `c ≥ 0`, the density `f c` of integers for which
`(p (n + 1) - p n) / log n < c` exists and is a continuous function of `c`?
-/
@[category research open, AMS 11]
theorem erdos_234 : answer(sorry) ↔ ∃ f : ℝ≥0 → ℝ, Continuous f ∧
    ∀ c : ℝ≥0, HasDensity {n : ℕ | (primeGap n : ℝ) / (n : ℝ).log < c} (f c) := by
  sorry

end Erdos234
