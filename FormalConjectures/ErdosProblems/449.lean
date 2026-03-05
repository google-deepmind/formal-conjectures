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
# Erdős Problem 449

*Reference:* [erdosproblems.com/449](https://www.erdosproblems.com/449)

Let $r(n)$ count the number of pairs $(d_1, d_2)$ such that $d_1 \mid n$ and
$d_2 \mid n$ and $d_1 < d_2 < 2d_1$. Is it true that, for every $\epsilon > 0$,
$r(n) < \epsilon \tau(n)$ for almost all $n$, where $\tau(n)$ is the number of
divisors of $n$?

This is false. For any constant $K > 0$, we have $r(n) > K\tau(n)$ for a
positive density set of $n$. Kevin Ford observed this follows from the negative
solution to [448] via the Cauchy–Schwarz inequality.
-/

open Classical

namespace Erdos449

/-- $r(n)$: the number of ordered pairs $(d_1, d_2)$ of divisors of $n$ with
$d_1 < d_2 < 2 \cdot d_1$. -/
def closeDivisorPairs (n : ℕ) : ℕ :=
  ((n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2 ∧ p.2 < 2 * p.1)).card

/-- Erdős Problem 449 (DISPROVED by Ford, via the negative solution to [448]):

Is it true that for every $\epsilon > 0$, $r(n) < \epsilon \cdot \tau(n)$ for
almost all $n$? The answer is no. -/
@[category research solved, AMS 11]
theorem erdos_449 : answer(False) ↔
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 N).filter (fun n =>
        (closeDivisorPairs n : ℝ) ≥ ε * (n.divisors.card : ℝ))).card /
          (N : ℝ) < δ := by
  sorry

end Erdos449
