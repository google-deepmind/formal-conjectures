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
# Erdős Problem 1114

*Reference:* [erdosproblems.com/1114](https://www.erdosproblems.com/1114)

[Ba60b] Balint, proved the conjecture on monotonicity of gaps between consecutive
zeros of the derivative of a polynomial with roots in arithmetic progression.
-/

open scoped BigOperators
open Polynomial Finset

namespace Erdos1114

/--
Erdős Problem 1114 (proved by Balint [Ba60b]):

Let $f(x) \in \mathbb{R}[x]$ be a polynomial whose $(n+1)$ roots are all real, distinct, and
form an arithmetic progression: $a, a+d, a+2d, \ldots, a+nd$ for some $a \in \mathbb{R}$, $d > 0$.
By Rolle's theorem, $f'(x)$ has $n$ distinct real zeros $b_0 < b_1 < \cdots < b_{n-1}$
in the interval $(a, a+nd)$.

The conjecture (now proved) states that the differences between consecutive
zeros of $f'(x)$ are monotonically increasing from the midpoint towards the
endpoints. By symmetry of the arithmetic progression, the zeros of $f'$ are
symmetric about the center point, so it suffices to state the monotonicity
for the right half: for indices $i, j$ with $\lfloor(n-1)/2\rfloor \leq i < j$ and $j+1 < n$,
we have $b_{i+1} - b_i \leq b_{j+1} - b_j$.
-/
@[category research solved, AMS 26]
theorem erdos_1114 (n : ℕ) (hn : 2 ≤ n) (a d : ℝ) (hd : 0 < d) :
    let f := ∏ i ∈ range (n + 1), (X - C (a + ↑i * d))
    ∃ b : ℕ → ℝ,
      (∀ i j, i < n → j < n → i < j → b i < b j) ∧
      (∀ j, j < n → (derivative f).IsRoot (b j)) ∧
      (∀ x : ℝ, (derivative f).IsRoot x → ∃ j, j < n ∧ b j = x) ∧
      ∀ i j, (n - 1) / 2 ≤ i → i < j → j + 1 < n →
        b (i + 1) - b i ≤ b (j + 1) - b j := by
  sorry

end Erdos1114
