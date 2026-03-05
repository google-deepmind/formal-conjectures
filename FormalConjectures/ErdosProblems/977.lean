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
# Erdős Problem 977

Erdős asked whether the greatest prime factor of $2^n - 1$ grows faster than
linearly in $n$, i.e., whether $P(2^n - 1)/n \to \infty$.

*Reference:* [erdosproblems.com/977](https://www.erdosproblems.com/977)

[Er65b] Erdős, P., *On some problems in number theory*, 1965.

[St13] Stewart, C. L., *On divisors of Fermat, Fibonacci, Lucas, and Lehmer numbers*, 2013.
-/

open Filter

namespace Erdos977

/-- The greatest prime divisor of $n$, or $0$ if $n \leq 1$. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactors.sup id

/--
Erdős Problem #977 [Er65b]:
If $P(m)$ denotes the greatest prime divisor of $m$, is it true that
$P(2^n - 1) / n \to \infty$ as $n \to \infty$?

This was proved by Stewart [St13], who showed that
$P(2^n - 1) \gg n^{1 + 1/(104 \log \log n)}$ for all sufficiently large $n$.
-/
@[category research solved, AMS 11]
theorem erdos_977 :
    answer(True) ↔
      Tendsto (fun n : ℕ => (greatestPrimeFactor (2 ^ n - 1) : ℝ) / (n : ℝ))
        atTop atTop := by
  sorry

end Erdos977
