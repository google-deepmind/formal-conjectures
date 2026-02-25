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
# Erdős Problem 884

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)
-/

open scoped BigOperators

namespace Erdos884

/--
Let $n \in \mathbb{N}$, and let $d_1 < \cdots < d_t$ be the (positive) divisors of $n$.
Is it true that
$$
  \sum_{1\le i<j\le t}\frac{1}{d_j-d_i}
  \ll 1+\sum_{1\le i<t}\frac{1}{d_{i+1}-d_i},
$$
with an absolute implied constant?
-/
@[category research open, AMS 11]
theorem erdos_884 :
    answer(sorry) ↔
      ∃ C > (0 : ℝ), ∀ n : ℕ, n ≠ 0 →
        let ds : List ℕ := (Nat.divisors n).sort (· ≤ ·)
        let gapRecipSum : ℝ :=
          (ds.zipWith (fun a b : ℕ ↦ (1 : ℝ) / ((b - a : ℕ) : ℝ)) ds.tail).sum
        let pairRecipSum : ℝ :=
          (Nat.divisors n).sum fun d₁ =>
            (Nat.divisors n).sum fun d₂ =>
              if d₁ < d₂ then (1 : ℝ) / ((d₂ - d₁ : ℕ) : ℝ) else 0
        pairRecipSum ≤ C * (1 + gapRecipSum) := by
  sorry

end Erdos884
