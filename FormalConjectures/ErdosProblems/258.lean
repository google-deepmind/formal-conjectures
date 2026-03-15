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
# Erdős Problem 258

*Reference:* [erdosproblems.com/258](https://www.erdosproblems.com/258)
-/

namespace Erdos258

/--
Let $a_1 \leq a_2 \leq \cdots$ be integers with $a_i \geq 2$ and $a_n \to \infty$. Is
$\sum_n \frac{d(n)}{a_1 \cdots a_n}$ irrational, where $d(n)$ is the number of divisors of $n$?
-/
@[category research open, AMS 11]
theorem erdos_258 : answer(sorry) ↔ ∀ (a : ℕ → ℕ), (∀ n, 2 ≤ a n) →
    Filter.Tendsto a Filter.atTop Filter.atTop →
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / ∏ i ∈ Finset.Icc 1 (n + 1), a i)) := by
  sorry


/--
Let $2 \leq a_1 \leq a_2 \leq \cdots$ be a monotone sequence with $a_n \to \infty$.
Is $\sum_n \frac{d(n)}{a_1 \cdots a_n}$ irrational, where $d(n)$ is the number of divisors of $n$?

Solution: True (proved by Erdős and Straus [ErSt71], Lemma 2.2 and Theorem 2.13).
-/
@[category research solved, AMS 11]
theorem erdos_258.variants.monotone : answer(True) ↔
    ∀ (a : ℕ → ℕ), (∀ n, 2 ≤ a n) → Monotone a →
    Filter.Tendsto a Filter.atTop Filter.atTop →
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / ∏ i ∈ Finset.Icc 1 (n + 1), a i)) := by
  sorry


/--
Is $\sum_n \frac{d(n)}{t^n}$ irrational, where $t ≥ 2$ is an integer.

Solution: True (proved by Erdős, see Erdős Problems website)
-/
@[category research solved, AMS 11]
theorem erdos_258.variants.Constant : answer(True) ↔ ∀ t ≥ (2 : ℕ),
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / t^(n + 1))) := by
  sorry

end Erdos258
