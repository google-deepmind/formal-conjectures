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
# Erdős Problem 120

*Reference:* [erdosproblems.com/120](https://www.erdosproblems.com/120)
-/

open Set MeasureTheory

namespace Erdos120

/--
Let $A ⊆ R$ be an infinite set. Must there be a set $E ⊂ R$ of positive measure which
does not contain any set of the shape $aA + b$ for some $a,b ∈ R$ and $a ≠ 0$?
-/
@[category research open, AMS 05 28]
theorem erdos_120 :
   answer(sorry) ↔ ∀ (A : Set ℝ), A.Infinite →
   ∃ E : Set ℝ,
   volume E > 0 ∧ ∃ a b : ℝ, a ≠ 0 ∧ ¬(Set.image (fun x => a * x + b) A ⊆ E) := by
  sorry

end Erdos120
