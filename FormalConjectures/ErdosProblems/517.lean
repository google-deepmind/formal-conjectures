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
-/

open Set

namespace Erdos517

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `nₖ / k → ∞`, then `f` assumes every value
infinitely often. -/
@[category research open, AMS 30]
theorem erdos_517.fabry {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

/-- The following theorem is proved in [Bi28]. -/
@[category research solved, AMS 30]
theorem erdos_517.fejer {f : ℂ → ℂ} (z : ℂ) : {x : ℂ | f x = z}.Infinite := by
  sorry

end Erdos517
