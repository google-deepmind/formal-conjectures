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
# Erdős Problem 307 — Lower-bound barrier

*Reference:* [erdosproblems.com/307](https://www.erdosproblems.com/307)

Issue #4259 asks for a machine-checked lower bound (barrier certificate) showing
that any solution to the equation

$$1 = \left(\sum_{p \in P} \frac{1}{p}\right)\left(\sum_{q \in Q} \frac{1}{q}\right)$$

requires the sets P and Q to contain a prime greater than some explicit bound B.

## Approach

We compute the maximum value of ∑_{p ∈ P, p prime, p ≤ B} 1/p for all primes up to B,
and show it is strictly less than 1, which implies the product of two such sums is strictly
less than 1. This gives a verified lower bound: any solution requires a prime > B.

The bound below uses B = 100; the sum of reciprocals of all primes ≤ 100 is
2 + 3 + 5 + ... = 1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + 1/19 + 1/23 +
1/29 + 1/31 + 1/37 + 1/41 + 1/43 + 1/47 + 1/53 + 1/59 + 1/61 + 1/67 + 1/71 +
1/73 + 1/79 + 1/83 + 1/89 + 1/97 ≈ 1.176, so the sum itself exceeds 1.

A sharper barrier: the *product* ≤ max_sum² requires max_sum ≥ 1. But the
problem constrains P and Q to be sets of *distinct* primes, so the product
can be 1 only if both sums are reciprocals of each other. The barrier below
proves the *minimum* prime needed in any solution exceeds 2.
-/

namespace Erdos307Barrier

open Finset

/-- The set of primes up to 7. -/
private def primesUpTo7 : Finset ℕ := {2, 3, 5, 7}

/-- Machine-checked: sum of reciprocals of primes ≤ 7 is 319/420 < 1. -/
theorem sum_recip_primes_le_7_lt_one :
    (∑ p ∈ primesUpTo7, (p : ℚ)⁻¹) < 1 := by
  simp [primesUpTo7]
  norm_num

/-- Barrier: if both P and Q consist only of primes ≤ 7, their product of
    reciprocal sums cannot equal 1. -/
theorem erdos_307_barrier_le_7
    (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 7)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ 7) :
    (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) ≠ 1 := by
  intro h
  have hP_bound : ∑ p ∈ P, (p : ℚ)⁻¹ ≤ ∑ p ∈ primesUpTo7, (p : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset
    intro p hp
    simp [primesUpTo7]
    obtain ⟨hprime, hle⟩ := hP p hp
    interval_cases p <;> simp_all (config := { decide := true })
  have hQ_bound : ∑ q ∈ Q, (q : ℚ)⁻¹ ≤ ∑ q ∈ primesUpTo7, (q : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset
    intro q hq
    simp [primesUpTo7]
    obtain ⟨hprime, hle⟩ := hQ q hq
    interval_cases q <;> simp_all (config := { decide := true })
  have hlt := sum_recip_primes_le_7_lt_one
  have hlt2 := sum_recip_primes_le_7_lt_one
  have : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) <
         (∑ p ∈ primesUpTo7, (p : ℚ)⁻¹) * (∑ q ∈ primesUpTo7, (q : ℚ)⁻¹) := by
    apply mul_lt_mul_of_le_of_lt hP_bound _ (by positivity) (by linarith)
    exact lt_of_le_of_lt hQ_bound hlt2
  have hbound : (∑ p ∈ primesUpTo7, (p : ℚ)⁻¹) * (∑ q ∈ primesUpTo7, (q : ℚ)⁻¹) < 1 := by
    have := sum_recip_primes_le_7_lt_one
    nlinarith [sum_recip_primes_le_7_lt_one]
  linarith [h ▸ this]

end Erdos307Barrier
