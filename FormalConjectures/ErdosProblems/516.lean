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
# Erdős Problem 516
*Reference:*
 - [erdosproblems.com/516](https://www.erdosproblems.com/516)
-/

open scoped Real
open Set Filter

/-- An entire function `f` is said to be of finite order if there exist numbers c, a ≥ 0
such that for all `z`, `‖f z‖ ≤ c * rexp ‖z‖ ^ a`. -/
def ofFiniteOrder {E F: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ 0, ∃ a ≥ 0, ∀ z, ‖f z‖ ≤ c * rexp ‖z‖ ^ a

namespace Erdos516

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function of finite order such that ? -/
@[category research open, AMS 30]
theorem erdos_517.fabry {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `∑ 1 / nₖ < ∞`, then `f` assumes every value
infinitely often. This theorem is proved in [Bi28]. -/
@[category research solved, AMS 30]
theorem erdos_517.fejer {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

end Erdos516
