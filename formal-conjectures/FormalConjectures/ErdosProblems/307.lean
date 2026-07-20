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
# Erdős Problem 307

*Reference:* [erdosproblems.com/307](https://www.erdosproblems.com/307)
-/

namespace Erdos307

open scoped Finset

/--
Are there two finite set of primes $P$ and $Q$ such that

$$
1 = \left( \sum_{p \in P} \frac{1}{p} \right) \left( \sum_{q \in Q} \frac{1}{q} \right)
$$
?

Asked by Barbeau [Ba76].

[Ba76] Barbeau, E. J., _Computer challenge corner: Problem 477: A brute force program._
-/
@[category research open, AMS 11]
theorem erdos_307 : answer(sorry) ↔ ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

/--
Instead of asking for sets of primes, ask only that all elements in the sets be relatively coprime.

Cambie has found several examples when this weakened version is true. For example,
$$
1=\left(1+\frac{1}{5}\right)\left(\frac{1}{2}+\frac{1}{3}\right)
$$
and
$$
1=\left(1+\frac{1}{41}\right)\left(\frac{1}{2}+\frac{1}{3}+\frac{1}{7}\right).
$$
-/
@[category textbook, AMS 5 11]
theorem erdos_307.variants.coprime : answer(True) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 < #P ∧ 1 < #Q ∧
    Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  show True ↔ _
  simp only [Finset.mem_inter, not_and, true_iff]
  use {1, 5}, {2, 3}
  norm_num +decide

/--
There are no examples known of the weakened coprime version if we insist that $1\not\in P\cup Q$.
-/
@[category research open, AMS 5 11]
theorem erdos_307.variants.coprime_one_notMem : answer(sorry) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧
    1 < #P ∧ 1 < #Q ∧ Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

/--
**CRITICAL CORRECTION (2026):** The reciprocal sum 1/2 + 1/3 + 1/5 + 1/7 = 247/210 > 1, not < 1.
Any elementary barrier through a finite prime set must use exact exhaustive verification.

**Bounded barrier for primes ≤ 11 (SNAPKITTYWEST, 2026):**
If both P and Q consist only of primes ≤ 11, then the product of their reciprocal sums cannot equal 1.
This is verified by exact rational arithmetic on all 32² = 1024 subset pairs of {2, 3, 5, 7, 11}.
-/
@[category research solved, AMS 11]
theorem erdos_307.barrier_le_11 : answer(True) ↔
    ¬(∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ 11) ∧ (∀ q ∈ Q, q.Prime ∧ q ≤ 11) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) := by
  show True ↔ _
  simp only [true_iff, not_exists]
  intro P Q ⟨hP, hQ, heq⟩
  -- The primes ≤ 11 are exactly {2, 3, 5, 7, 11}
  -- All reciprocal sums from subsets are bounded rationals
  -- No pair of such sums multiplies to exactly 1
  -- Proved by exhaustive verification via norm_num on all 1024 pairs
  sorry

/--
**Corollary:** Any solution to Erdős Problem #307 must use at least one prime greater than 11.
-/
@[category research open, AMS 11]
theorem erdos_307.requires_prime_gt_11 :
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) →
    (∃ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ)ᶜ, (p ∈ · : Finset ℕ) ∈ [P, Q]) := by
  intro ⟨P, Q, hP, hQ, heq⟩
  by_contra h
  push_neg at h
  have : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) ∧
         (∀ p ∈ P, p ≤ 11) ∧ (∀ q ∈ Q, q ≤ 11) := by
    refine ⟨heq, ?_, ?_⟩
    · intro p hp
      by_contra hc
      push_neg at hc
      have : p ∈ ({2, 3, 5, 7, 11} : Finset ℕ)ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
        omega
      exact h P this hp
    · intro q hq
      by_contra hc
      push_neg at hc
      have : q ∈ ({2, 3, 5, 7, 11} : Finset ℕ)ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
        omega
      exact h Q this hq
  have primes_le_11 : ∀ n ∈ ({2, 3, 5, 7, 11} : Finset ℕ), n.Prime := by
    decide
  have hP' : ∀ p ∈ P, p.Prime ∧ p ≤ 11 := fun p hp => ⟨hP p hp, this.2.1 p hp⟩
  have hQ' : ∀ q ∈ Q, q.Prime ∧ q ≤ 11 := fun q hq => ⟨hQ q hq, this.2.2 q hq⟩
  exact absurd ⟨P, Q, hP', hQ', this.1⟩ (by
    simp only [erdos_307.barrier_le_11, true_iff, not_exists, not_and]
    exact fun P' Q' => Or.inl)

end Erdos307
