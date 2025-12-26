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
# Erdős Problem 517

*Reference:*
 - [erdosproblems.com/517](https://www.erdosproblems.com/517)
 - [Bi28] Biernacki, Miécislas, Sur les équations algébriques contenant des paramétres arbitraires.
    (1928), 145.
 - [Wa01] Wang, Yuefei. "On the Fatou set of an entire function with gaps." Tohoku Mathematical
    Journal, Second Series 53.1 (2001): 163-170.
-/

open Set Filter

namespace Erdos517

/-- This is the terminology adopted in [Wa01] and some other sources. -/
def hasFejerGaps (n : ℕ → ℕ) : Prop := Tendsto (fun k => n k / (k : ℝ)) atTop atTop

def hasFabryGaps (n : ℕ → ℕ) : Prop := Summable (fun k => 1 / (n k : ℝ))

@[category API, AMS 40]
theorem hasFabryGaps.hasFejerGaps {n : ℕ → ℕ} (hn : hasFabryGaps n) : hasFejerGaps n := by
  sorry

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

end Erdos517
