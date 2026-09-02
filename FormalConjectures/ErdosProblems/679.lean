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
# Erdős Problem 679

*Reference:* [erdosproblems.com/679](https://www.erdosproblems.com/679)
-/

namespace Erdos679

/--
Let $\omega(n)$ denote the number of distinct prime factors of $n$. For every $\varepsilon>0$,
are there infinitely many $n$ such that
$$\omega(n-k)<(1+\varepsilon)\frac{\log k}{\log\log k}$$
for every sufficiently large $k<n$, where the threshold for $k$ depends only on $\varepsilon$?
-/
@[category research open, AMS 11]
theorem erdos_679 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, K ≤ k → k < n →
        ((n - k).primeFactors.card : ℝ) <
          (1 + ε) * Real.log k / Real.log (Real.log k) := by
  sorry

end Erdos679
