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
# Erdős Problem 967

Let $1 < a_1 < a_2 < \cdots$ be a strictly increasing sequence of integers with
$\sum 1/a_k < \infty$. Is it necessarily true that for every real $t$,
$1 + \sum_k a_k^{-(1+it)} \neq 0$? Yip showed the answer is no.

*Reference:* [erdosproblems.com/967](https://www.erdosproblems.com/967)

[ErIn64] Erdős, P. and Ingham, A. E., *Arithmetical Tauberian theorems*, Acta Arithmetica (1964).

[Yi25] Yip, C. H., *On a question of Erdős and Ingham* (2025).
-/

open Complex

namespace Erdos967

/--
Erdős Problem 967 (Disproved by Yip [Yi25]):

Let $1 < a_1 < a_2 < \cdots$ be a strictly increasing sequence of integers with
$\sum 1/a_k < \infty$. Erdős and Ingham [ErIn64] asked whether it is necessarily true
that for every real $t$,
$$1 + \sum_k a_k^{-(1+it)} \neq 0.$$

Yip proved that for any real $t \neq 0$, there exists such a sequence satisfying
$$1 + \sum_k a_k^{-(1+it)} = 0.$$

It remains open whether this holds for every finite sequence of integers.
-/
@[category research solved, AMS 11 30]
theorem erdos_967 :
    answer(False) ↔
      (∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 2 ≤ a i) →
        Summable (fun i => (1 : ℝ) / (a i : ℝ)) →
        ∀ t : ℝ, 1 + (∑' k, (1 : ℂ) / ((a k : ℂ) ^ ((1 : ℂ) + ↑t * I))) ≠ 0) := by
  sorry

end Erdos967
