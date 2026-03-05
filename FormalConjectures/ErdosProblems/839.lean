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
# Erdős Problem 839

*Reference:* [erdosproblems.com/839](https://www.erdosproblems.com/839)

Given a strictly increasing sequence of positive integers where no term equals the sum of
consecutive earlier terms, is it true that $\limsup a_n / n = \infty$? A stronger form asks
whether $(1/\log x) \sum_{a_n < x} 1/a_n \to 0$.

A problem of Erdős [Er78f][Er92c].

[Er78f] Erdős, P., *Problems in number theory and combinatorics*, Proc. Sixth Manitoba Conf. on
Numerical Math. (1978), 35-58.

[Er92c] Erdős, P., *Some of my favourite unsolved problems*, J. Combin. Theory Ser. A (1992).
-/

open Filter Real Finset

namespace Erdos839

/-- A sequence $a : \mathbb{N} \to \mathbb{N}$ is "sum-of-consecutive-free" if no term equals
the sum of a contiguous block of earlier terms. That is, for all $i$,
$a_i \neq a_j + a_{j+1} + \cdots + a_k$ for any $j \leq k < i$. -/
def SumOfConsecutiveFree (a : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, ∀ j k : ℕ, j ≤ k → k < i →
    a i ≠ ∑ l ∈ Finset.Icc j k, a l

/--
Erdős Problem 839 (Part 1) [Er78f][Er92c]:

Let $1 \leq a_1 < a_2 < \cdots$ be a strictly increasing sequence of positive integers
such that no $a_i$ is the sum of consecutive $a_j$ for $j < i$.
Is it true that $\limsup a_n / n = \infty$?
-/
@[category research open, AMS 11]
theorem erdos_839 : answer(sorry) ↔
    ∀ (a : ℕ → ℕ), (∀ n, 1 ≤ a n) → StrictMono a → SumOfConsecutiveFree a →
    ∀ M : ℝ, ∃ᶠ n in atTop, M < (a n : ℝ) / (n : ℝ) := by
  sorry

/--
Erdős Problem 839 (Part 2, stronger) [Er78f][Er92c]:

Let $1 \leq a_1 < a_2 < \cdots$ be a strictly increasing sequence of positive integers
such that no $a_i$ is the sum of consecutive $a_j$ for $j < i$.
Is it true that $\lim_{x \to \infty} \frac{1}{\log x} \sum_{a_n < x} \frac{1}{a_n} = 0$?
-/
@[category research open, AMS 11]
theorem erdos_839.variants.stronger : answer(sorry) ↔
    ∀ (a : ℕ → ℕ), (∀ n, 1 ≤ a n) → StrictMono a → SumOfConsecutiveFree a →
    Tendsto (fun x : ℕ =>
      (∑ n ∈ (Finset.range x).filter (fun n => a n < x), (1 / (a n : ℝ))) /
      Real.log (x : ℝ))
      atTop (nhds 0) := by
  sorry

end Erdos839
