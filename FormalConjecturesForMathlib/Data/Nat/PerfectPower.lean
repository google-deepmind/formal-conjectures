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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Nat

/--
A [perfect power](https://en.wikipedia.org/wiki/Perfect_power) is a natural number that
  is a product of equal natural factors, or, in other words, an integer that can be expressed
  as a square or a higher integer power of another integer greater than one. More formally,
  $n$ is a perfect power if there exist natural numbers $m > 1$, and $k > 1$ such that
  $m ^ k = n$. In this case, $n$ may be called a perfect $k$th power. If $k = 2$ or
  $k = 3$, then $n$ is called a perfect square or perfect cube, respectively.
-/
def IsPerfectPower (n : ℕ) : Prop :=
    ∃ k m : ℕ, 1 < k ∧ 1 < m ∧ k ^ m = n

theorem isPerfectPower_iff_factorization_gcd (n : ℕ) :
    IsPerfectPower n ↔ n > 1 ∧ n.primeFactors.gcd n.factorization > 1 := by
  constructor
  · -- Forward direction: IsPerfectPower n → n > 1 ∧ gcd > 1
    intro ⟨k, m, hk, hm, hpow⟩
    constructor
    · -- n > 1
      have h : n ≥ 4 := by
        calc n = k ^ m := hpow.symm
          _ ≥ 2 ^ m := Nat.pow_le_pow_left hk m
          _ ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
      omega
    · -- gcd > 1
      subst hpow
      have hk_pos : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (le_of_lt hk)
      have hm_pos : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (le_of_lt hm)
      rw [Nat.factorization_pow, primeFactors_pow k hm_pos]
      -- m divides every exponent, so gcd ≥ m > 1
      have h_nonempty := nonempty_primeFactors.mpr hk
      obtain ⟨p, hp⟩ := h_nonempty
      -- Show m divides the gcd
      have h_m_dvd_gcd : m ∣ k.primeFactors.gcd (m • k.factorization) := by
        apply Finset.dvd_gcd
        intro b _
        show m ∣ (m • k.factorization) b
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact dvd_mul_right m _
      -- The gcd is positive because k has at least one prime factor with positive exponent
      have hp_in_support : p ∈ k.factorization.support := by
        rw [support_factorization]; exact hp
      have hp_exp_pos : 0 < k.factorization p := Finsupp.mem_support_iff.mp hp_in_support |> Nat.pos_of_ne_zero
      have h_gcd_pos : 0 < k.primeFactors.gcd (m • k.factorization) := by
        have h1 := Finset.gcd_dvd (f := (m • k.factorization)) hp
        have h_eq : (m • k.factorization) p = m * k.factorization p := by
          simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [h_eq] at h1
        have h_val_pos : 0 < m * k.factorization p := Nat.mul_pos (Nat.pos_of_ne_zero hm_pos) hp_exp_pos
        exact Nat.pos_of_dvd_of_pos h1 h_val_pos
      exact Nat.lt_of_lt_of_le hm (Nat.le_of_dvd h_gcd_pos h_m_dvd_gcd)
  · -- Backward direction: n > 1 ∧ gcd > 1 → IsPerfectPower n
    intro ⟨hn, hgcd⟩
    set g := n.primeFactors.gcd n.factorization with hg_def
    -- Define k as the product of p^(n.factorization p / g) for all primes p | n
    let f : ℕ → ℕ := fun q => q ^ (n.factorization q / g)
    set k := n.primeFactors.prod f with hk_def
    use k, g
    refine ⟨?_, hgcd, ?_⟩
    · -- k > 1
      have h_nonempty := nonempty_primeFactors.mpr hn
      obtain ⟨p, hp⟩ := h_nonempty
      have hp_prime := prime_of_mem_primeFactors hp
      -- p ∈ n.primeFactors means n.factorization p > 0
      have hp_in_support : p ∈ n.factorization.support := by
        rw [support_factorization]; exact hp
      have hp_pos : 0 < n.factorization p := Finsupp.mem_support_iff.mp hp_in_support |> Nat.pos_of_ne_zero
      have h_div : g ∣ n.factorization p := Finset.gcd_dvd hp
      have hg_pos : 0 < g := Nat.lt_trans Nat.zero_lt_one hgcd
      have h_quot_pos : 0 < n.factorization p / g :=
        Nat.div_pos (Nat.le_of_dvd hp_pos h_div) hg_pos
      have h_ge_p : k ≥ f p := by
        rw [hk_def]
        exact Finset.single_le_prod' (f := f)
          (fun q hq => Nat.one_le_pow _ _ (Prime.one_le (prime_of_mem_primeFactors hq))) hp
      have h_ge_2 : f p ≥ 2 := by
        show p ^ (n.factorization p / g) ≥ 2
        calc p ^ (n.factorization p / g) ≥ p ^ 1 := Nat.pow_le_pow_right (Prime.one_le hp_prime) h_quot_pos
          _ = p := pow_one p
          _ ≥ 2 := Prime.two_le hp_prime
      omega
    · -- k ^ g = n
      have h_eq : k ^ g = n.primeFactors.prod (fun q => q ^ (n.factorization q / g * g)) := by
        rw [hk_def, ← Finset.prod_pow]
        congr 1
        ext q
        show (f q) ^ g = q ^ (n.factorization q / g * g)
        simp only [f, ← pow_mul]
      rw [h_eq]
      have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_succ_lt hn)
      conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn_ne_zero]
      congr 1
      ext p
      by_cases hp : p ∈ n.primeFactors
      · have h_div : g ∣ n.factorization p := Finset.gcd_dvd hp
        rw [Nat.div_mul_cancel h_div]
      · -- p ∉ n.primeFactors means n.factorization p = 0
        have hp_not_in_support : p ∉ n.factorization.support := by
          rw [support_factorization]; exact hp
        have hp_zero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not_in_support
        simp only [hp_zero, Nat.zero_div, zero_mul, pow_zero]

instance IsPerfectPower.decide : ∀ n, Decidable (IsPerfectPower n) := fun n =>
  decidable_of_iff (n > 1 ∧ n.primeFactors.gcd n.factorization > 1)
    (isPerfectPower_iff_factorization_gcd n).symm

example : IsPerfectPower 4 := by native_decide
example : IsPerfectPower 27 := by native_decide
example : ¬IsPerfectPower 0 := by native_decide
example : ¬IsPerfectPower 1 := by native_decide
example : ¬IsPerfectPower 2 := by native_decide

end Nat
