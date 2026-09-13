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

import FormalConjecturesUtil

/-!
# Erdős Problem 1053

*Reference:* [erdosproblems.com/1053](https://www.erdosproblems.com/1053)
-/

open Filter Real
open scoped Topology

namespace Erdos1053

/-- `n` is $k$-perfect if $\sigma(n)=kn$, where $\sigma(n)$ is the sum of the divisors of $n$. -/
def IsKPerfect (k n : ℕ) : Prop :=
  (∑ d ∈ n.divisors, d) = k * n

/--
Call a number $k$-perfect if $\sigma(n)=kn$, where $\sigma(n)$ is the sum of the divisors of $n$.
Must $k=o(\log\log n)$?
-/
@[category research open, AMS 11]
theorem erdos_1053 :
    answer(sorry) ↔
      ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ n k : ℕ, 1 < n → IsKPerfect k n → N ≤ n →
          (k : ℝ) ≤ ε * log (log n) := by
  sorry

end Erdos1053
