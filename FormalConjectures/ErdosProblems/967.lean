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
import FormalConjecturesForMathlib.Analysis.HasGaps

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
$\sum 1/a_k < \infty$ (i.e., the sequence has Fejér gaps). Erdős and Ingham [ErIn64] asked
whether it is necessarily true that for every real $t$,
$$1 + \sum_k a_k^{-(1+it)} \neq 0.$$

Yip proved that for any real $t \neq 0$, there exists such a sequence satisfying
$$1 + \sum_k a_k^{-(1+it)} = 0.$$
-/
@[category research solved, AMS 11 30]
theorem erdos_967 :
    answer(False) ↔
      (∀ (a : ℕ → ℕ), HasFejerGaps a → (∀ i, 2 ≤ a i) →
        ∀ t : ℝ, 1 + (∑' k, (1 : ℂ) / ((a k : ℂ) ^ ((1 : ℂ) + ↑t * I))) ≠ 0) := by
  sorry

/--
Erdős Problem 967 (Finite-sequence variant, Open):

The finite-sequence analogue of Erdős Problem 967: for any finite set $S$ of integers
greater than 1, is it true that $1 + \sum_{a \in S} a^{-(1+it)} \neq 0$ for every real $t$?

This remains open even for the simplest case $S = \{2, 3, 5\}$, which Erdős and Ingham [ErIn64]
could not resolve. The Four Exponentials Conjecture would imply non-vanishing in the
$\{2, 3, 5\}$ case.
-/
@[category research open, AMS 11 30]
theorem erdos_967_finite :
    ∀ (S : Finset ℕ), (∀ a ∈ S, 2 ≤ a) →
      ∀ t : ℝ, 1 + (∑ a ∈ S, (1 : ℂ) / ((a : ℂ) ^ ((1 : ℂ) + ↑t * I))) ≠ 0 := by
  sorry

/--
Erdős Problem 967 (The $\{2, 3, 5\}$ case, Open):

The simplest open case of the finite-sequence variant: is it true that
$2^{-(1+it)} + 3^{-(1+it)} + 5^{-(1+it)} \neq -1$ for every real $t$?

Erdős and Ingham [ErIn64] highlighted this as the simplest case they could not decide.
The Four Exponentials Conjecture implies this never vanishes.
-/
@[category research open, AMS 11 30]
theorem erdos_967_235 :
    ∀ t : ℝ, 1 + ((1 : ℂ) / ((2 : ℂ) ^ ((1 : ℂ) + ↑t * I)) +
      (1 : ℂ) / ((3 : ℂ) ^ ((1 : ℂ) + ↑t * I)) +
      (1 : ℂ) / ((5 : ℂ) ^ ((1 : ℂ) + ↑t * I))) ≠ 0 := by
  sorry

end Erdos967
