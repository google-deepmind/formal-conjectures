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
# Erdős Problem 1200

*References:*
- [erdosproblems.com/1200](https://www.erdosproblems.com/1200)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErRu80] Erdős, P. and Ruzsa, I. Z., *On the small sieve. I. Sifting by primes*. J. Number
  Theory (1980), 385-394.
-/

open Filter Finset

namespace Erdos1200

/--
There exists a constant $C$ such that for all large $x$ there is a collection of primes
$p_1<\ldots<p_k<x$ with $\sum\frac{1}{p_i}<C$ together with a system of congruences
$a_i\pmod{p_i}$ such that every integer $n<x$ satisfies at least one of these congruences.
-/
@[category research open, AMS 11]
theorem erdos_1200 : answer(sorry) ↔
    ∃ C > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∃ (P : Finset ℕ) (a : ℕ → ℕ),
        (∀ p ∈ P, p.Prime ∧ p < x) ∧
          (∑ p ∈ P, (1 : ℝ) / p) < C ∧
          ∀ n < x, ∃ p ∈ P, n ≡ a p [MOD p] := by
  sorry

/--
Erdős and Ruzsa proved that for any $C>0$ there exists a set of primes $P$ such that
$\sum_{p\in P}\frac{1}{p}\leq C$ and the number of integers $n\leq x$ divisible by at least one
$p\in P$ is $\gg_C x$.
-/
@[category research solved, AMS 11]
theorem erdos_1200.variants.erdos_ruzsa (C : ℝ) (hC : 0 < C) :
    ∃ c > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime) ∧
          (∑ p ∈ P, (1 : ℝ) / p) ≤ C ∧
          c * x ≤ ((range (x + 1)).filter fun n => ∃ p ∈ P, p ∣ n).card := by
  sorry

end Erdos1200
