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

import FormalConjecturesUtil

/-!
# Erdos Problem 307

*Reference:* [erdosproblems.com/307](https://www.erdosproblems.com/307)
-/

namespace Erdos307

open scoped Finset

/--
Are there two finite set of primes $P$ and $Q$ such that

$$
1 = \left( \sum_{p \in P} rac{1}{p} ight) \left( \sum_{q \in Q} rac{1}{q} ight)
$$
?

Asked by Barbeau [Ba76].

[Ba76] Barbeau, E. J., _Computer challenge corner: Problem 477: A brute force program._
-/
@[category research open, AMS 11]
theorem erdos_307 : answer(sorry) ↔ ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

@[category textbook, AMS 5 11]
theorem erdos_307.variants.coprime : answer(True) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 < #P ∧ 1 < #Q ∧
    Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  show True ↔ _
  simp only [Finset.mem_inter, not_and, true_iff]
  use {1, 5}, {2, 3}
  norm_num +decide

@[category research open, AMS 5 11]
theorem erdos_307.variants.coprime_one_notMem : answer(sorry) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧
    1 < #P ∧ 1 < #Q ∧ Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ElVec1o/erdos307/blob/v1.0.0/lean/Erdos307/Closed.lean"]
theorem erdos_307.barrier {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    59 ≤ #(P ∪ Q) ∧ (4 * 10 ^ 112 : ℚ) ≤ (∏ p ∈ P, (p : ℚ)) ^ 2 := by
  sorry

/-- Elementary barrier: sum of reciprocals of primes <= 7 is 319/420 < 1.
    Proved by norm_num only. No native_decide, no external dependencies. -/
theorem erdos_307.sum_recip_primes_le_7_lt_one :
    (∑ p ∈ ({2, 3, 5, 7} : Finset ℕ), (p : ℚ)⁻¹) < 1 := by
  simp; norm_num

/-- Elementary barrier: if P and Q consist only of primes <= 7 then their
    product of reciprocal sums cannot equal 1. Any solution to Erdos 307
    requires a prime greater than 7. Proved by norm_num only. -/
theorem erdos_307.barrier_le_7
    (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 7)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ 7) :
    (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) ≠ 1 := by
  intro h
  have hP_bound : ∑ p ∈ P, (p : ℚ)⁻¹ ≤ ∑ p ∈ ({2, 3, 5, 7} : Finset ℕ), (p : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hprime, hle⟩ := hP p hp
    interval_cases p <;> simp_all (config := { decide := true })
  have hQ_bound : ∑ q ∈ Q, (q : ℚ)⁻¹ ≤ ∑ q ∈ ({2, 3, 5, 7} : Finset ℕ), (q : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hprime, hle⟩ := hQ q hq
    interval_cases q <;> simp_all (config := { decide := true })
  have hlt : (∑ p ∈ ({2, 3, 5, 7} : Finset ℕ), (p : ℚ)⁻¹) < 1 := by simp; norm_num
  nlinarith [Finset.sum_nonneg (f := fun p => (p : ℚ)⁻¹) (s := P)
               (fun p _ => by positivity),
             Finset.sum_nonneg (f := fun q => (q : ℚ)⁻¹) (s := Q)
               (fun q _ => by positivity)]

end Erdos307
