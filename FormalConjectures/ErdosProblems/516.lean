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

open Set Filter

def ofFiniteOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Prop :=
  ∃ c

namespace Erdos516

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `nₖ / k → ∞`, is it true that `f` assumes
every value infinitely often? -/
@[category research open, AMS 30]
theorem erdos_517.fabry {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `∑ 1 / nₖ < ∞`, then `f` assumes every value
infinitely often. This theorem is proved in [Bi28]. -/
@[category research solved, AMS 30]
theorem erdos_517.fejer {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

end Erdos516
