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
# Erdős Problem 828

*Reference:* [erdosproblems.com/828](https://www.erdosproblems.com/828)
-/

namespace Erdos828

open scoped Nat

/--
Is it true that, for any $a \in \mathbb{Z}$, there are infinitely many $n$ such that
$$\phi(n) | n + a$$?
-/
@[category research open, AMS 11]
theorem erdos_828 : answer(sorry) ↔ ∀ a : ℤ, Set.Infinite {n : ℕ | ↑(φ n) ∣ n + a} := by
  sorry

/--
When $n > 1$, Lehmer conjectured that $\phi(n) | n - 1$ if and only if $n$ is prime.
-/
@[category research open, AMS 11]
theorem erdos_828.variants.lehmer_conjecture : answer(sorry) ↔ ∀ n > 1, φ n ∣ n - 1 ↔ Prime n := by
  sorry

/--
It is an easy exercise to show that $\phi(n) | n$ if and only if $n = 0, 1$ or $n = 2^a 3^b$ for
some $a > 0$.
-/
@[category undergraduate, AMS 11]
theorem erdos_828.variants.phi_dvd_self_iff_pow2_pow3 {n : ℕ} :
    φ n ∣ n ↔ n ≤ 1 ∨ ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b := by
  constructor
  revert n
  intro n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  intro h
  by_cases h1 : n ≤ 1
  exact Or.inl h1
  right
  push_neg at h1
  by_cases h6 : n ≤ 6
  interval_cases n
  exact ⟨1, by omega, 0, by norm_num⟩
  exact absurd h (by decide)
  exact ⟨2, by omega, 0, by norm_num⟩
  exact absurd h (by decide)
  exact ⟨1, by omega, 1, by norm_num⟩
  push_neg at h6
  have h_even : Even n := h.even (Nat.totient_even (by omega))
  obtain ⟨m, hm⟩ := h_even
  have hm2 : n = 2 * m := by omega
  have hm_lt : m < n := by omega
  have hm_pos : 0 < m := by omega
  by_cases hm_odd : Odd m
  rw [hm2] at h
  rw [Nat.totient_two_mul_of_odd hm_odd] at h
  by_cases hm1 : m = 1
  subst hm1; exact ⟨1, by omega, 0, by rw [hm2]; norm_num⟩
  by_cases hm_prime : m.Prime
  rw [Nat.totient_prime hm_prime] at h
  have h_eq : 2 * m = (m - 1) * 2 + 2 := by omega
  rw [h_eq] at h
  have h_dvd2 : (m - 1) ∣ 2 := (Nat.dvd_add_right (dvd_mul_right _ 2)).mp h
  have hm3 : m = 3 := by have := Nat.le_of_dvd (by omega) h_dvd2; omega
  subst hm3; exact ⟨1, by omega, 1, by rw [hm2]; norm_num⟩
  by_cases hm_pp : IsPrimePow m
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hm_pp
  rw [Nat.totient_prime_pow hp hk] at h
  have hpk : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
  have h_rw : 2 * p ^ k = p ^ (k - 1) * (2 * p) := by rw [hpk]; ring
  rw [h_rw] at h
  have h_cancel : (p - 1) ∣ 2 * p := (Nat.mul_dvd_mul_iff_left (pos_of_ne_zero (pow_ne_zero _ hp.ne_zero))).mp h
  have h_eq2 : 2 * p = (p - 1) * 2 + 2 := by have := hp.one_lt; omega
  rw [h_eq2] at h_cancel
  have h_dvd2 : (p - 1) ∣ 2 := (Nat.dvd_add_right (dvd_mul_right _ 2)).mp h_cancel
  have hp_le : p ≤ 3 := by have := Nat.le_of_dvd (by omega) h_dvd2; omega
  have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact hm_odd.not_two_dvd_nat (dvd_pow_self 2 (by omega))
  have hp3 : p = 3 := by have := hp.two_le; omega
  subst hp3; exact ⟨1, by omega, k, by rw [hm2]; ring⟩
  exfalso
  have hm2_le : 2 ≤ m := by omega
  have hm_ne : m ≠ 0 := by omega
  have h_card : m.primeFactors.card ≠ 1 := (isPrimePow_iff_card_primeFactors_eq_one.not.mp hm_pp)
  have h_card_pos : 0 < m.primeFactors.card := by
    rw [Finset.card_pos]; exact ⟨m.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, hm_ne⟩⟩
  have h_card_ge2 : 2 ≤ m.primeFactors.card := by omega
  obtain ⟨p, hp_mem, q, hq_mem, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < m.primeFactors.card)
  have hp := Nat.prime_of_mem_primeFactors hp_mem
  have hq := Nat.prime_of_mem_primeFactors hq_mem
  have h_decomp := Nat.ordProj_mul_ordCompl_eq_self m p
  have h_cop := (Nat.coprime_pow_left_iff (Nat.Prime.factorization_pos_of_dvd hp hm_ne (Nat.dvd_of_mem_primeFactors hp_mem)) p (ordCompl[p] m)).mpr (Nat.coprime_ordCompl hp hm_ne)
  have h_phi := Nat.totient_mul h_cop
  rw [h_decomp] at h_phi
  have hp_odd : p ≠ 2 := by intro hp2; subst hp2; exact hm_odd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
  have h_fact_pos := Nat.Prime.factorization_pos_of_dvd hp hm_ne (Nat.dvd_of_mem_primeFactors hp_mem)
  have hp_le_proj : p ≤ ordProj[p] m := Nat.le_self_pow h_fact_pos.ne' p
  have hp_ge3 : 3 ≤ ordProj[p] m := by have := hp.two_le; omega
  have hcop_pq : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  have hq_dvd := Nat.dvd_of_mem_primeFactors hq_mem
  rw [← h_decomp] at hq_dvd
  have hq_dvd_oc : q ∣ ordCompl[p] m := (hcop_pq.pow_right _).dvd_of_dvd_mul_left hq_dvd
  have hq_odd : q ≠ 2 := by intro hq2; subst hq2; exact hm_odd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hq_mem)
  have hq_ge3 : 3 ≤ ordCompl[p] m := by have := Nat.le_of_dvd (Nat.ordCompl_pos p hm_ne) hq_dvd_oc; have := hq.two_le; omega
  have h_even1 : Even (φ (ordProj[p] m)) := Nat.totient_even hp_ge3
  have h_even2 : Even (φ (ordCompl[p] m)) := Nat.totient_even hq_ge3
  obtain ⟨a, ha⟩ := h_even1
  obtain ⟨b, hb⟩ := h_even2
  have h4 : 4 ∣ φ m := ⟨a * b, by rw [h_phi, ha, hb]; ring⟩
  have h4_2m : 4 ∣ 2 * m := dvd_trans h4 h
  exact hm_odd.not_two_dvd_nat ⟨m / 2, by omega⟩
  have hm_even : Even m := by rwa [Nat.not_odd_iff_even] at hm_odd
  rw [hm2] at h
  rw [Nat.totient_two_mul_of_even hm_even] at h
  have h_dvd : m.totient ∣ m := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2) h
  rcases ih m hm_lt h_dvd with hle | ⟨a, ha, b, hab⟩
  omega
  exact ⟨a + 1, by omega, b, by rw [hm2, hab]; ring⟩
  rintro (h | ⟨a, ha, b, rfl⟩)
  · interval_cases n <;> simp
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  by_cases hb : b = 0
  subst hb
  simp [Nat.totient_prime_pow_succ Nat.prime_two]
  exact Nat.pow_dvd_pow 2 (Nat.le_succ a)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hcop : Nat.Coprime (2 ^ (a + 1)) (3 ^ (b + 1)) := ((Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by omega)).pow _ _
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two, Nat.totient_prime_pow_succ Nat.prime_three]
  show 2 ^ a * (2 - 1) * (3 ^ b * (3 - 1)) ∣ 2 ^ (a + 1) * 3 ^ (b + 1)
  norm_num [pow_succ]
  rw [show 2 ^ a * (3 ^ b * 2) = 2 ^ a * 2 * 3 ^ b from by ring, show 2 ^ a * 2 * (3 ^ b * 3) = 2 ^ a * 2 * 3 ^ b * 3 from by ring]
  exact dvd_mul_right _ 3

end Erdos828
