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
# Polignac's conjecture (consecutive prime gaps)

Polignac's conjecture (1849) asserts that for every positive even integer $k$ there are
infinitely many indices $n$ such that the gap between consecutive primes equals $k$:
$$p_{n+1} - p_n = k$$
(where $p_n$ is the $n$-th prime, $0$-indexed as in `Nat.nth Nat.Prime`).

Special cases include consecutive gaps of size $2$ (twin primes), $4$ (cousin primes) and
$6$ (sexy primes).

Related but distinct from `Dickson.polignac_conjecture` in
`FormalConjectures/Wikipedia/Dickson.lean`, which asks for infinitely many primes $p$ such that
$p + 2k$ is also prime (not necessarily successive in the prime list). The consecutive-gap
form is strictly stronger for $k > 2$. See also `TwinPrimes.twin_primes` for the classical
formulation of the twin prime conjecture.

Zhang (2013), Maynard (2015) and Polymath imply that some even gap $k \le 246$ occurs
infinitely often as a consecutive prime gap.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Polignac%27s_conjecture)
- Y. Zhang, *Bounded gaps between primes*, Ann. of Math. 179 (2014), 1121–1174
- J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383–413
-/

namespace Polignac

/-- Gap between the $n$-th and $(n+1)$-st prime (`Nat.nth Nat.Prime` is $0$-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- Indices $n$ at which the consecutive prime gap equals $k$. -/
def gapEquals (k : ℕ) : Set ℕ :=
  {n | primeGap n = k}

@[category API, AMS 11]
theorem mem_gapEquals_iff {k n : ℕ} : n ∈ gapEquals k ↔ primeGap n = k := by
  simp [gapEquals]

/--
**Polignac's conjecture (consecutive form).** For every positive even integer $k$, the gap
$k$ occurs for infinitely many pairs of consecutive primes.
-/
@[category research open, AMS 11]
theorem polignac_conjecture (k : ℕ) (hk_pos : 0 < k) (hk_even : Even k) :
    (gapEquals k).Infinite := by
  sorry

/-- Special case $k = 2$: consecutive prime gaps equal to $2$ (twin primes). -/
@[category textbook, AMS 11]
theorem polignac_conjecture.variants.gap_two
    (H : type_of% polignac_conjecture) : (gapEquals 2).Infinite :=
  H 2 (by norm_num) (by decide)

/-- Special case $k = 4$: consecutive prime gaps equal to $4$. -/
@[category textbook, AMS 11]
theorem polignac_conjecture.variants.gap_four
    (H : type_of% polignac_conjecture) : (gapEquals 4).Infinite :=
  H 4 (by norm_num) (by decide)

/-- Special case $k = 6$: consecutive prime gaps equal to $6$. -/
@[category textbook, AMS 11]
theorem polignac_conjecture.variants.gap_six
    (H : type_of% polignac_conjecture) : (gapEquals 6).Infinite :=
  H 6 (by norm_num) (by decide)

/--
**Bounded gaps (Zhang / Maynard / Polymath).** There exists a positive even integer
$k \le 246$ that occurs infinitely often as a consecutive prime gap.

Finitary form of $\liminf_{n\to\infty}(p_{n+1}-p_n)\le 246$.
-/
@[category research solved, AMS 11]
theorem bounded_gaps_polymath :
    ∃ k : ℕ, 0 < k ∧ k ≤ 246 ∧ Even k ∧ (gapEquals k).Infinite := by
  sorry

/-- $p_1 - p_0 = 3 - 2 = 1$. -/
@[category test, AMS 11]
theorem primeGap_zero : primeGap 0 = 1 := by
  norm_num [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- $p_2 - p_1 = 5 - 3 = 2$. -/
@[category test, AMS 11]
theorem primeGap_one : primeGap 1 = 2 := by
  norm_num [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- $p_3 - p_2 = 7 - 5 = 2$. -/
@[category test, AMS 11]
theorem primeGap_two : primeGap 2 = 2 := by
  norm_num [primeGap, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

@[category test, AMS 11]
theorem one_mem_gapEquals_two : 1 ∈ gapEquals 2 := by
  rw [mem_gapEquals_iff, primeGap_one]

@[category test, AMS 11]
theorem two_mem_gapEquals_two : 2 ∈ gapEquals 2 := by
  rw [mem_gapEquals_iff, primeGap_two]

@[category test, AMS 11]
theorem zero_not_mem_gapEquals_two : 0 ∉ gapEquals 2 := by
  rw [mem_gapEquals_iff, primeGap_zero]
  norm_num

end Polignac
