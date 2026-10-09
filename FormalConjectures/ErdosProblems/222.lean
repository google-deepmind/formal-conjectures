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

public import Mathlib

/-!
# Erdős Problem #222: gaps between sums of two squares

Let `n₀ < n₁ < n₂ < ⋯` be the natural numbers which are sums of two squares
(`0, 1, 2, 4, 5, 8, 9, 10, 13, …`, OEIS A001481).  Erdős asked to *explore the behaviour*
of (i.e. find good upper and lower bounds for) the consecutive differences `n_{k+1} - n_k`.

The problem is listed as **open**: it is an open-ended request for sharp bounds, and
it has no single yes/no answer.  This file contains:

* the definition of the sequence (`Erdos222.sumTwoSq`);
* a **proof** of the upper bound of Bambah and Chowla (1947), with explicit constants:
  `n_{k+1} - n_k ≤ 2 + (64 (n_k + 1))^{1/4}` (`Erdos222.sumTwoSq_gap_le`), and hence
  `n_{k+1} - n_k = O(n_k^{1/4})` (`Erdos222.sumTwoSq_gap_isBigO`);
* a **proof** that the gaps are unbounded (`Erdos222.sumTwoSq_gap_unbounded`), a weak form of
  the lower bounds of Erdős (1951) and Richards (1982);
* the *statement* (not a proof) of Richards' theorem
  `limsup (n_{k+1} - n_k) / log n_k ≥ 1/4` (`Erdos222.RichardsLowerBound`).
-/

@[expose] public section

namespace Erdos222

open Filter Asymptotics

/-- `n` is a sum of two squares of natural numbers (equivalently, of integers). -/
def IsSumTwoSq (n : ℕ) : Prop := ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- The `k`-th sum of two squares, indexed from `0` (so `sumTwoSq 0 = 0`, `sumTwoSq 1 = 1`,
`sumTwoSq 2 = 2`, `sumTwoSq 3 = 4`, …). -/
noncomputable def sumTwoSq (k : ℕ) : ℕ := Nat.nth IsSumTwoSq k

lemma isSumTwoSq_zero : IsSumTwoSq 0 := ⟨0, 0, by simp⟩

lemma infinite_setOf_isSumTwoSq : (Set.ofPred IsSumTwoSq).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => n ^ 2)
    (Nat.pow_left_injective two_ne_zero) fun n => ⟨n, 0, by simp⟩

lemma sumTwoSq_strictMono : StrictMono sumTwoSq :=
  Nat.nth_strictMono infinite_setOf_isSumTwoSq

lemma isSumTwoSq_sumTwoSq (k : ℕ) : IsSumTwoSq (sumTwoSq k) :=
  Nat.nth_mem_of_infinite infinite_setOf_isSumTwoSq k

@[simp] lemma sumTwoSq_zero : sumTwoSq 0 = 0 :=
  Nat.nth_zero_of_zero isSumTwoSq_zero

/-- The next term after `n_k` is at most any sum of two squares exceeding `n_k`. -/
lemma sumTwoSq_succ_le {k s : ℕ} (hs : IsSumTwoSq s) (hlt : sumTwoSq k < s) :
    sumTwoSq (k + 1) ≤ s := by
  obtain ⟨j, -, rfl⟩ := Nat.exists_lt_card_nth_eq hs
  have hkj : k < j := sumTwoSq_strictMono.lt_iff_lt.mp hlt
  exact sumTwoSq_strictMono.monotone hkj

/-! ### The upper bound of Bambah and Chowla -/

/-- For every `m` there is a sum of two squares `s` with `m < s ≤ m + 2 + t`, where
`t ^ 4 ≤ 64 (m + 1)`. -/
lemma exists_isSumTwoSq_near (m : ℕ) :
    ∃ s t : ℕ, IsSumTwoSq s ∧ m < s ∧ s ≤ m + 2 + t ∧ t ^ 4 ≤ 64 * (m + 1) := by
  obtain ⟨a, ha, ha'⟩ : ∃ a : ℕ, a * a ≤ m + 1 ∧ m + 1 < (a + 1) * (a + 1) :=
    ⟨_, Nat.sqrt_le _, Nat.lt_succ_sqrt _⟩
  obtain ⟨r, hr⟩ : ∃ r, m + 1 = a * a + r := ⟨m + 1 - a * a, by omega⟩
  obtain ⟨b, hb, hb'⟩ : ∃ b : ℕ, b * b ≤ r ∧ r < (b + 1) * (b + 1) :=
    ⟨_, Nat.sqrt_le _, Nat.lt_succ_sqrt _⟩
  have hr2 : r ≤ 2 * a := by nlinarith
  refine ⟨a ^ 2 + (b + 1) ^ 2, 2 * b, ⟨a, b + 1, rfl⟩, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h1 : (b * b) * (b * b) ≤ r * r := Nat.mul_le_mul hb hb
    have h2 : r * r ≤ (2 * a) * (2 * a) := Nat.mul_le_mul hr2 hr2
    nlinarith

/-- **Bambah–Chowla** (explicit form): `n_{k+1} - n_k ≤ 2 + t` for some `t` with
`t ^ 4 ≤ 64 (n_k + 1)`. -/
lemma sumTwoSq_gap_le_nat (k : ℕ) :
    ∃ t : ℕ, sumTwoSq (k + 1) ≤ sumTwoSq k + 2 + t ∧ t ^ 4 ≤ 64 * (sumTwoSq k + 1) := by
  obtain ⟨s, t, hs, hlt, hle, ht⟩ := exists_isSumTwoSq_near (sumTwoSq k)
  exact ⟨t, (sumTwoSq_succ_le hs hlt).trans hle, ht⟩

/-- **Bambah–Chowla** (1947), with explicit constants:
`n_{k+1} - n_k ≤ 2 + (64 (n_k + 1))^{1/4}`. -/
theorem sumTwoSq_gap_le (k : ℕ) :
    ((sumTwoSq (k + 1) : ℝ) - sumTwoSq k) ≤ 2 + (64 * ((sumTwoSq k : ℝ) + 1)) ^ (1 / 4 : ℝ) := by
  obtain ⟨t, hle, ht⟩ := sumTwoSq_gap_le_nat k
  have hle' : (sumTwoSq (k + 1) : ℝ) ≤ sumTwoSq k + 2 + t := by exact_mod_cast hle
  have ht' : ((t : ℝ) ^ 4) ≤ 64 * ((sumTwoSq k : ℝ) + 1) := by exact_mod_cast ht
  have htt : (t : ℝ) ≤ (64 * ((sumTwoSq k : ℝ) + 1)) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) ht' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h
    norm_num at h
    exact h
  linarith

/-- **Bambah–Chowla** (1947): `n_{k+1} - n_k ≪ n_k^{1/4}`. -/
theorem sumTwoSq_gap_isBigO :
    (fun k => ((sumTwoSq (k + 1) : ℝ) - sumTwoSq k)) =O[atTop]
      fun k => ((sumTwoSq k : ℝ)) ^ (1 / 4 : ℝ) := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hm : (1 : ℝ) ≤ sumTwoSq k := by
    have : sumTwoSq 0 < sumTwoSq k := sumTwoSq_strictMono (by omega)
    simp only [sumTwoSq_zero] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) ≤ (sumTwoSq (k + 1) : ℝ) - sumTwoSq k := by
    have := sumTwoSq_strictMono (Nat.lt_succ_self k)
    have : (sumTwoSq k : ℝ) < sumTwoSq (k + 1) := by exact_mod_cast this
    linarith
  set m : ℝ := (sumTwoSq k : ℝ)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have h1 : (1 : ℝ) ≤ m ^ (1 / 4 : ℝ) := Real.one_le_rpow hm (by norm_num)
  have h2 : (64 * (m + 1)) ^ (1 / 4 : ℝ) ≤ 4 * m ^ (1 / 4 : ℝ) := by
    calc (64 * (m + 1)) ^ (1 / 4 : ℝ) ≤ (256 * m) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (256 : ℝ) ^ (1 / 4 : ℝ) * m ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hm0
      _ = 4 * m ^ (1 / 4 : ℝ) := by
          congr 1
          rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hg := sumTwoSq_gap_le k
  rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg (by positivity)]
  linarith

/-! ### The gaps are unbounded -/

/-- If a prime `p ≡ 3 (mod 4)` divides `n` exactly once, then `n` is not a sum of two squares. -/
lemma not_isSumTwoSq_of_modEq {p n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hn : n ≡ p [MOD p ^ 2]) : ¬ IsSumTwoSq n := by
  have := Fact.mk hp
  have hp2 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  have hmod : n % p ^ 2 = p := by
    rw [hn]; exact Nat.mod_eq_of_lt hp2
  set c := n / p ^ 2
  have hn' : n = p * (p * c + 1) := by
    have := Nat.div_add_mod n (p ^ 2)
    rw [hmod] at this
    rw [← this]; ring
  have hndvd : ¬ p ∣ p * c + 1 := by
    intro h
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p c)).mp h
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hval : padicValNat p n = 1 := by
    rw [hn', padicValNat.mul hp.ne_zero (by omega), padicValNat.self hp.one_lt,
      padicValNat.eq_zero_of_not_dvd hndvd]
  intro ⟨x, y, hxy⟩
  have h := Nat.eq_sq_add_sq_iff.mp ⟨x, y, hxy⟩ p ?_ hp4
  · rw [hval] at h
    exact Nat.not_even_one h
  · rw [Nat.mem_primeFactors]
    exact ⟨hp, hn' ▸ dvd_mul_right _ _, by rw [hn']; exact mul_ne_zero hp.ne_zero (by omega)⟩

/-- The set of primes congruent to `3` modulo `4`. -/
lemma infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3}.Infinite :=
  Nat.infinite_setOfPred_prime_and_eq_mod (by decide)

/-- For every `L` there is `N` such that none of `N, N + 1, …, N + L - 1` is a sum of
two squares. -/
lemma exists_long_run_not_isSumTwoSq (L : ℕ) :
    ∃ N : ℕ, ∀ i < L, ¬ IsSumTwoSq (N + i) := by
  set S := {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3}
  set p : ℕ → ℕ := Nat.nth (· ∈ S)
  have hpS : ∀ i, p i ∈ S := Nat.nth_mem_of_infinite infinite_setOf_prime_mod_four_eq_three
  have hpinj : Function.Injective p :=
    (Nat.nth_strictMono infinite_setOf_prime_mod_four_eq_three).injective
  have hprime : ∀ i, (p i).Prime := fun i => (hpS i).1
  have hp4 : ∀ i, p i % 4 = 3 := fun i => by
    have h := (hpS i).2
    have : ((p i : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using h
    simpa using (ZMod.natCast_eq_natCast_iff' (p i) 3 4).mp this
  obtain ⟨N, hN⟩ := Nat.chineseRemainderOfFinset (fun i => p i + L * p i ^ 2 - i)
    (fun i => p i ^ 2) (Finset.range L)
    (fun i _ => pow_ne_zero 2 (hprime i).ne_zero)
    (fun i _ j _ hij => by
      simp only [Function.onFun]
      exact Nat.Coprime.pow 2 2
        ((Nat.coprime_primes (hprime i) (hprime j)).mpr (hpinj.ne hij)))
  refine ⟨N, fun i hi => not_isSumTwoSq_of_modEq (hprime i) (hp4 i) ?_⟩
  have h := (hN i (Finset.mem_range.mpr hi)).add_right i
  have hpp : 1 ≤ p i ^ 2 := Nat.one_le_pow _ _ (hprime i).pos
  have hL : L ≤ L * p i ^ 2 := Nat.le_mul_of_pos_right L hpp
  have heq : p i + L * p i ^ 2 - i + i = p i + p i ^ 2 * L := by
    rw [mul_comm (p i ^ 2) L]; omega
  rw [heq] at h
  refine h.trans ?_
  simp [Nat.ModEq]

/-- The gaps `n_{k+1} - n_k` between consecutive sums of two squares are unbounded. -/
theorem sumTwoSq_gap_unbounded (L : ℕ) : ∃ k, L ≤ sumTwoSq (k + 1) - sumTwoSq k := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact ⟨0, Nat.zero_le _⟩
  obtain ⟨N, hN⟩ := exists_long_run_not_isSumTwoSq L
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exact absurd isSumTwoSq_zero (by simpa using hN 0 hL)
    · exact h
  have hex : ∃ j, N ≤ sumTwoSq j := ⟨N, sumTwoSq_strictMono.id_le N⟩
  set j := Nat.find hex
  have hj : N ≤ sumTwoSq j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h
    have := hj
    rw [h, sumTwoSq_zero] at this
    omega
  obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := Nat.exists_eq_succ_of_ne_zero hj0
  have hkN : sumTwoSq k < N := by
    have := Nat.find_min hex (show k < j by omega)
    omega
  refine ⟨k, ?_⟩
  rw [← hk]
  have hge : N + L ≤ sumTwoSq j := by
    by_contra hcon
    exact hN (sumTwoSq j - N) (by omega) (by
      rw [Nat.add_sub_cancel' hj]; exact isSumTwoSq_sumTwoSq j)
  omega

/-! ### Statement of a known lower bound (not proved here) -/

/-- **Richards (1982)** (statement only, not proved in this file):
`limsup_{k → ∞} (n_{k+1} - n_k) / log n_k ≥ 1/4`, phrased without `limsup` as: for every
`c < 1/4`, infinitely often `n_{k+1} - n_k ≥ c log n_k`.
The constant has since been improved to `0.868…` by Dietmann–Elsholtz–Kalmynin–Konyagin–
Maynard (2022). -/
def RichardsLowerBound : Prop :=
  ∀ c : ℝ, c < 1 / 4 →
    ∃ᶠ k in atTop, c * Real.log (sumTwoSq k) ≤ (sumTwoSq (k + 1) : ℝ) - sumTwoSq k

end Erdos222

end
