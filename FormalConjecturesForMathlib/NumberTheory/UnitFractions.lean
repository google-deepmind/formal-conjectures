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
module

public import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic.NormNum

/-!
# Prime-power obstructions to Egyptian fractions

A sum of distinct reciprocals of positive integers cannot equal one if its largest
denominator is a positive prime power. The proof separates the largest term using
the nonarchimedean p-adic norm.

This is the prime-power observation in [Erdős problem 292](https://www.erdosproblems.com/292).
-/

@[expose] public section

namespace EgyptianFraction

private theorem padicNorm_nat_inv {p a : ℕ} [Fact p.Prime] (ha : a ≠ 0) :
    padicNorm p ((a : ℚ)⁻¹) = (p : ℚ) ^ padicValNat p a := by
  rw [padicNorm.eq_zpow_of_nonzero (inv_ne_zero (Nat.cast_ne_zero.mpr ha)),
    padicValRat.inv, padicValRat.of_nat, neg_neg, zpow_natCast]

/-- A positive prime power is the unique largest p-adic denominator among
positive integers up to itself, so their distinct reciprocals cannot sum to one. -/
theorem sum_reciprocals_ne_one_of_max_prime_pow {p k : ℕ} (S : Finset ℕ)
    (hp : p.Prime) (hk : 0 < k)
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ p ^ k) (hn : p ^ k ∈ S) :
    (∑ a ∈ S, (1 : ℚ) / a) ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpq : 1 < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hpk : 1 < (p : ℚ) ^ k := one_lt_pow₀ hpq (Nat.ne_of_gt hk)
  have hmax : padicNorm p ((1 : ℚ) / (p ^ k : ℕ)) = (p : ℚ) ^ k := by
    rw [one_div, padicNorm_nat_inv (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow]
  have hrest : padicNorm p (∑ a ∈ S.erase (p ^ k), (1 : ℚ) / a) < (p : ℚ) ^ k := by
    apply padicNorm.sum_lt' _ (lt_trans (by norm_num) hpk)
    intro a ha
    obtain ⟨hane, haS⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha1, hale⟩ := hS a haS
    have ha0 : a ≠ 0 := by omega
    have halt : a < p ^ k := lt_of_le_of_ne hale hane
    have hv : padicValNat p a < k := by
      by_contra hv
      have hd : p ^ k ∣ a := (padicValNat_dvd_iff_le ha0).mpr (by omega)
      exact (not_le_of_gt halt) (Nat.le_of_dvd (by omega) hd)
    rw [one_div, padicNorm_nat_inv ha0]
    exact pow_lt_pow_right₀ hpq hv
  intro heq
  have hsplit : (1 : ℚ) / (p ^ k : ℕ) +
      ∑ a ∈ S.erase (p ^ k), (1 : ℚ) / a = 1 := by
    rw [Finset.add_sum_erase S (fun a ↦ (1 : ℚ) / a) hn, heq]
  have hnorm := padicNorm.add_eq_max_of_ne
    (q := (1 : ℚ) / (p ^ k : ℕ))
    (r := ∑ a ∈ S.erase (p ^ k), (1 : ℚ) / a)
    (by rw [hmax]; exact ne_of_gt hrest)
  rw [hsplit, padicNorm.one, hmax, max_eq_left (le_of_lt hrest)] at hnorm
  exact (ne_of_lt hpk) hnorm

end EgyptianFraction
