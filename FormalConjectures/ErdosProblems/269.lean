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
# Erdős Problem 269

*Reference:* [erdosproblems.com/269](https://www.erdosproblems.com/269)
-/

namespace Erdos269
/--
A positive integer $n$ has all its prime factors in the set $P$.
By convention, $1$ satisfies this for any $P$ as it has no prime divisors.
-/
def HasPrimeFactorsIn (P : Set ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ∈ P

/--
The infinite, strictly increasing sequence $\{a_0, a_1, \dots\}$ of integers
whose prime factors all belong to `P`.
-/
noncomputable def a (P : Set ℕ) : ℕ → ℕ := Nat.nth <| HasPrimeFactorsIn P

/--
The `n`-th partial least common multiple, $[a_0, \dots, a_n]$, which is
the LCM of the first `n` integers in the sequence.
-/
noncomputable def partialLcm (P : Set ℕ) (n : ℕ) : ℕ :=
  -- We take the LCM of `{a P 0, ..., a P n}`.
  (Finset.range n).lcm (a P)

/--
The sum $\sum_{n=1}^\infty \frac{1}{[a_0,\ldots,a_{n - 1}]}$.
-/
noncomputable def series (P : Set ℕ) : ℝ :=  ∑' n, (1 : ℝ) / (partialLcm P n)

/--
Let $P$ be a finite set of primes with $|P| \ge 2$ and let
$\{a_1 < a_2 < \dots\}$ be the set of positive integers whose prime factors
are all in $P$. Is the sum
$$ \sum_{n=1}^\infty \frac{1}{[a_1,\ldots,a_n]} $$
rational or irrational?
-/
@[category research open, AMS 11]
theorem erdos_269 : (∀ᵉ (P : Finset ℕ) (h : ∀ p ∈ P, p.Prime) (h_card : P.card ≥ 2),
    (Irrational (series (P : Set ℕ)) ↔ answer(sorry))) ↔ answer(sorry) := by
  sorry

/--
This theorem addresses the case where the set of primes `P` is infinite. In this case the sum is
irrational.
-/
@[category research solved, AMS 11]
theorem erdos_269.variant.infinite (P : Set ℕ) (h : ∀ p ∈ P, p.Prime) (h_inf : P.Infinite) :
  Irrational (series P) := by
  sorry

end Erdos269
