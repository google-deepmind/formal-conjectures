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

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Prime-divisor generating series

The generating series of the number of distinct prime divisors, evaluated at one half,
can be rearranged into a sum over primes using absolute summability.
-/

@[expose] public section

open scoped ArithmeticFunction.omega

namespace ArithmeticFunction

/-- The number of distinct prime factors is the cardinality of `Nat.primeFactors`. -/
lemma cardDistinctFactors_eq_card_primeFactors (m : ℕ) : (ω m) = m.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- The term `primeDivTerm m p` is `(1 / 2) ^ m` when `p` is a prime dividing the positive
integer `m`, and `0` otherwise. -/
private noncomputable def primeDivTerm (m p : ℕ) : ℝ :=
  if p.Prime ∧ p ∣ m ∧ m ≠ 0 then (1 / 2 : ℝ) ^ m else 0

/-- Summing `primeDivTerm m p` over the primes `p` gives `ω m / 2 ^ m`. -/
private lemma tsum_primeDivTerm_right (m : ℕ) : ∑' p, primeDivTerm m p = (ω m : ℝ) / 2 ^ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [primeDivTerm]
  have hsupp : Function.support (primeDivTerm m) ⊆ ↑m.primeFactors := by
    intro p hp
    by_contra h
    apply hp
    have : ¬ (p.Prime ∧ p ∣ m) := fun ⟨h1, h2⟩ =>
      h (Finset.mem_coe.mpr (Nat.mem_primeFactors.mpr ⟨h1, h2, hm⟩))
    unfold primeDivTerm
    rw [if_neg (fun ⟨h1, h2, _⟩ => this ⟨h1, h2⟩)]
  rw [tsum_eq_sum (s := m.primeFactors) (fun p hp => by
    by_contra h
    exact hp (hsupp (by simpa using h)))]
  have : ∀ p ∈ m.primeFactors, primeDivTerm m p = (1 / 2 : ℝ) ^ m := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := Nat.mem_primeFactors.mp hp
    simp [primeDivTerm, h1, h2, hm]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul,
    cardDistinctFactors_eq_card_primeFactors]
  simp [div_eq_mul_inv]

/-- Summing `primeDivTerm m p` over `m` for a prime `p` gives `1 / (2 ^ p - 1)`. -/
private lemma tsum_primeDivTerm_left {p : ℕ} (hp : p.Prime) :
    ∑' m, primeDivTerm m p = 1 / (2 ^ p - 1 : ℝ) := by
  have hinj : Function.Injective (fun k : ℕ => p * (k + 1)) := by
    intro a b h
    have := Nat.eq_of_mul_eq_mul_left hp.pos h
    omega
  have hsupp : Function.support (fun m => primeDivTerm m p) ⊆
      Set.range (fun k : ℕ => p * (k + 1)) := by
    intro m hm
    have h : p.Prime ∧ p ∣ m ∧ m ≠ 0 := by
      by_contra h
      exact hm (by simp [primeDivTerm, h])
    obtain ⟨-, ⟨c, rfl⟩, hm0⟩ := h
    have hc : c ≠ 0 := fun h => hm0 (by simp [h])
    exact ⟨c - 1, by simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero hc)]⟩
  rw [← hinj.tsum_eq hsupp]
  have hr0 : (0 : ℝ) ≤ (1 / 2) ^ p := by positivity
  have hr1 : ((1 : ℝ) / 2) ^ p < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hp.ne_zero
  have : ∀ k : ℕ,
      primeDivTerm (p * (k + 1)) p = (1 / 2 : ℝ) ^ p * ((1 / 2 : ℝ) ^ p) ^ k := by
    intro k
    have h : p.Prime ∧ p ∣ p * (k + 1) ∧ p * (k + 1) ≠ 0 :=
      ⟨hp, dvd_mul_right _ _, by have := hp.pos; positivity⟩
    simp [primeDivTerm, h, pow_mul, pow_succ, mul_comm]
  rw [tsum_congr this, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h2 : (1 : ℝ) < 2 ^ p := one_lt_pow₀ (by norm_num) hp.ne_zero
  rw [one_div, inv_pow]
  have : (2 : ℝ) ^ p - 1 ≠ 0 := by linarith
  have h3 : (2 : ℝ) ^ p ≠ 0 := by positivity
  field_simp

/-- The double series defining `primeDivTerm` is summable. -/
private lemma summable_primeDivTerm : Summable (fun x : ℕ × ℕ => primeDivTerm x.1 x.2) := by
  have hnn : 0 ≤ (fun x : ℕ × ℕ => primeDivTerm x.1 x.2) := fun x => by
    simp only [Pi.zero_apply]
    unfold primeDivTerm
    split_ifs <;> positivity
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun m => ?_, ?_⟩
  · apply summable_of_hasFiniteSupport
    refine (Finset.range (m + 1)).finite_toSet.subset ?_
    intro p hp
    by_contra h
    apply hp
    have : ¬ (p.Prime ∧ p ∣ m ∧ m ≠ 0) := by
      rintro ⟨-, h2, h3⟩
      exact h (by simpa [Nat.lt_succ_iff] using Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2)
    simp [primeDivTerm, this]
  · have hs : Summable (fun m : ℕ => (m : ℝ) ^ 1 * (1 / 2 : ℝ) ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    refine Summable.of_nonneg_of_le (fun m => tsum_nonneg (fun p => hnn (m, p))) (fun m => ?_) hs
    simp only
    rw [tsum_primeDivTerm_right, one_div, inv_pow, pow_one, div_eq_mul_inv]
    have : (ω m : ℝ) ≤ m := by
      rw [cardDistinctFactors_eq_card_primeFactors]
      have hsub : m.primeFactors ⊆ Finset.Icc 1 m := by
        intro p hp
        obtain ⟨h1, h2, h3⟩ := Nat.mem_primeFactors.mp hp
        exact Finset.mem_Icc.mpr ⟨h1.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2⟩
      have := Finset.card_le_card hsub
      simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this (by positivity)

/-- The generating series for the number of distinct prime divisors converges at one half. -/
lemma summable_cardDistinctFactors_div_two_pow :
    Summable (fun n : ℕ => (ω n : ℝ) / 2 ^ n) :=
  summable_primeDivTerm.prod.congr (fun n => tsum_primeDivTerm_right n)

/-- The generating series for the number of distinct prime divisors, evaluated at one half,
is a sum over primes of reciprocals of Mersenne numbers. -/
lemma tsum_cardDistinctFactors_div_two_pow :
    ∑' n : ℕ, (ω n : ℝ) / 2 ^ n = ∑' p : {n : ℕ | n.Prime}, 1 / (2 ^ p.1 - 1) := by
  let A := { n : ℕ | n.Prime }
  have h2 : ∑' m : ℕ, (ω m : ℝ) / 2 ^ m = ∑' m, ∑' p, primeDivTerm m p :=
    tsum_congr fun m => (tsum_primeDivTerm_right m).symm
  have h3 : ∑' m, ∑' p, primeDivTerm m p = ∑' p, ∑' m, primeDivTerm m p :=
    (Summable.tsum_comm (f := primeDivTerm) summable_primeDivTerm).symm
  have h4 : ∑' p, ∑' m, primeDivTerm m p =
      ∑' p, A.indicator (fun p : ℕ => 1 / (2 ^ p - 1 : ℝ)) p := by
    refine tsum_congr fun p => ?_
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp, tsum_primeDivTerm_left hp]
    · rw [Set.indicator_of_notMem hp]
      have hp' : ¬ p.Prime := hp
      simp [primeDivTerm, hp']
  rw [h2, h3, h4, tsum_subtype A (fun p : ℕ => 1 / (2 ^ p - 1 : ℝ))]

end ArithmeticFunction
