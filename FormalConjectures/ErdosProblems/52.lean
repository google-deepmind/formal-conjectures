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
# Erdős Problem 52

*Reference:* [erdosproblems.com/52](https://www.erdosproblems.com/52)
-/

open scoped Pointwise

namespace Erdos52

/--
Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$
$\max( \lvert A+A\rvert,\lvert AA\rvert)\gg_\epsilon \lvert A\rvert^{2-\epsilon}?$
-/
@[category research open, AMS 11]
theorem erdos_52 : answer(sorry) ↔ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by
  sorry

-- TODO(firsching): Add addtional material.

end Erdos52
