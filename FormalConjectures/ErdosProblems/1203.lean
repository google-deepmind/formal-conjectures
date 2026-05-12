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
# Erdős Problem 1203

*References:*
- [erdosproblems.com/1203](https://www.erdosproblems.com/1203)
-/

open Filter Real
open scoped ArithmeticFunction.omega

namespace Erdos1203

/--
If $\omega(n)$ counts the number of distinct prime divisors of $n$ then let
$F(n)=\max_k \omega(n+k)\frac{\log\log k}{\log k}.$
-/
noncomputable def F (n : ℕ) : ℝ :=
  ⨆ k : ℕ, (ω (n + k) : ℝ) * (log (log (k : ℝ)) / log (k : ℝ))

/--
Prove that $F(n)\to \infty$ as $n\to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_1203 :
    answer(sorry) ↔ Tendsto F atTop atTop := by
  sorry

/--
It is easy to prove that $F(n)\geq 1-o(1)$.
-/
@[category research solved, AMS 11]
theorem erdos_1203.variants.lower_bound :
    ∀ ε > 0, ∀ᶠ n in atTop, F n ≥ 1 - ε := by
  sorry

end Erdos1203
