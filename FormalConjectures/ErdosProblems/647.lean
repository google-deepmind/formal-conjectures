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
# Erdős Problem 647

*Reference:* [erdosproblems.com/647](https://www.erdosproblems.com/647)
-/

namespace Erdos647

open Filter ArithmeticFunction.sigma

/-- Let $\tau(n)$ count the number of divisors of $n$. Is there some $n > 24$ such that
$$
  \max_{m < n}(m + \tau(m)) \leq n + 2?
$$ -/
@[category research open, AMS 11]
theorem erdos_647 : answer(sorry) ↔ ∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2 := by
  sorry

/-- This is true for $n = 24$. -/
@[category research solved, AMS 11]
theorem erdos_647.variants.twenty_four : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

/-- Erdős says 'it is extremely doubtful' that there are infinitely many such $n$, and in
fact suggests that
$$
  lim_{n\to\infty} \max_{m < n}(\tau(m) + m − n) = \infty.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.lim :
    answer(sorry) ↔ atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop := by
  sorry

/-- Erdős says it 'seems certain' that for every $k$ there are infinitely many $n$
for which
$$
  \max_{n−k < m < n}(m + \tau(m)) ≤ n + 2.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.infinite :
    answer(sorry) ↔ ∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite := by
  sorry

end Erdos647
