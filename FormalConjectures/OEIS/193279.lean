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

public import FormalConjecturesUtil

/-!
# Number of distinct sums of distinct proper divisors of $n$

The sequence $a(n)$ counts the number of distinct sums of non-empty subsets of the proper divisors
of $n$.

*References:*
- [A193279](https://oeis.org/A193279)
-/

@[expose] public section

namespace OeisA193279

/--
Number of distinct sums of distinct proper divisors of $n$ (excluding the empty sum $0$).
-/
def a (n : ℕ) : ℕ :=
  (n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x)).card - 1

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by decide

/--
If $n$ is an even perfect number, then $a(n) = n$.
- _Michael Engling_, Jul 20 2011
-/
@[category textbook, AMS 11]
theorem a_eq_self_of_perfect_of_even (n : ℕ) (hperf : n.Perfect) (heven : Even n) :
    a n = n := by
  set k := n.factorization 2
  set m := ordCompl[2] n
  set p := 2 ^ (k + 1) - 1
  have hk : 0 < k := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hperf.2.ne' (even_iff_two_dvd.mp heven)
  have hp_add : p + 1 = 2 ^ (k + 1) := Nat.sub_add_cancel Nat.one_le_two_pow
  have hp3 : 3 ≤ p := by have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ hk); omega
  have hcop_p : p.Coprime (2 ^ (k + 1)) := by rw [← hp_add]; simp
  have hn : n = 2 ^ k * p := by
    have hkm : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
    have h1 := geom_sum_mul_add 1 (k + 1)
    rw [← hkm, ((Nat.coprime_ordCompl Nat.prime_two hperf.2.ne').pow_left k).sum_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map] at hsum
    simp only [one_add_one_eq_two, mul_one, Function.Embedding.coeFn_mk] at h1 hsum
    rw [show ∑ i ∈ Finset.range (k + 1), 2 ^ i = p by omega, ← mul_assoc, ← pow_succ'] at hsum
    obtain ⟨j, hj⟩ : p ∣ m := hcop_p.dvd_of_dvd_mul_left ⟨_, hsum.symm⟩
    have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
      (show p * ∑ d ∈ m.divisors, d = p * (2 ^ (k + 1) * j) by rw [hsum, hj]; ring)
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, ← hp_add] at h2
    suffices j = 1 by rw [← hkm, hj, this, mul_one]
    by_contra hne
    have hj0 : 0 < j := Nat.pos_of_mul_pos_left (hj ▸ show 0 < m from Nat.ordCompl_pos 2 hperf.2.ne')
    nlinarith [show 1 + j ≤ ∑ x ∈ m.properDivisors, x from
      Finset.sum_pair (f := fun x : ℕ => x) (Ne.symm hne) ▸ Finset.sum_le_sum_of_subset
        (by simp [Finset.insert_subset_iff, Nat.mem_properDivisors, hj]; constructor <;> nlinarith)]
  suffices h : n.properDivisors.powerset.image (fun s => ∑ x ∈ s, x) = Finset.range (n + 1) by
    rw [a, h, Finset.card_range, Nat.add_sub_cancel]
  ext t; simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_range]
  have hps := (Nat.perfect_iff_sum_properDivisors hperf.2).mp hperf
  refine ⟨fun ⟨s, hs, hst⟩ => Nat.lt_succ_of_le
    (hst ▸ (Finset.sum_le_sum_of_subset hs).trans hps.le), fun ht => ?_⟩
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp ht) with htn | hlt
  · exact ⟨n.properDivisors, Finset.Subset.rfl, htn ▸ hps⟩
  have hbit (x d i : ℕ) (hx : x < 2 ^ d) (hi : i ∈ x.bitIndices.toFinset) : i < d :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp <| (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans_lt (by simpa)
  refine ⟨(t % p).bitIndices.toFinset.image (2 ^ ·) ∪ (t / p).bitIndices.toFinset.image (p * 2 ^ ·),
    Finset.union_subset (Finset.image_subset_iff.mpr fun i hi => ?_) (Finset.image_subset_iff.mpr fun i hi => ?_), ?_⟩
  · have hik := Nat.lt_succ_iff.mp (hbit _ (k + 1) i ((Nat.mod_lt t (by omega)).trans (by omega)) hi)
    exact Nat.mem_properDivisors.mpr ⟨(Nat.pow_dvd_pow 2 hik).trans ⟨p, hn⟩,
      by nlinarith [Nat.pow_le_pow_right (by decide : 0 < 2) hik, Nat.one_le_two_pow (n := k)]⟩
  · have hik := hbit _ k i (Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hn]; exact hlt)) hi
    exact Nat.mem_properDivisors.mpr ⟨hn ▸ mul_comm (2 ^ k) p ▸ mul_dvd_mul_left p (Nat.pow_dvd_pow 2 hik.le),
      by nlinarith [Nat.pow_lt_pow_right (by decide : 1 < 2) hik]⟩
  · have hinj := Nat.pow_right_injective (by decide : 2 ≤ 2)
    rw [Finset.sum_union (Finset.disjoint_left.mpr fun x hu hv => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu; obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hv
        have hci := (hcop_p.coprime_dvd_right (dvd_pow_self 2 k.succ_ne_zero)).pow_right i
        have := Nat.eq_one_of_dvd_one (hci.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl ⟨2 ^ j', hj'.symm⟩); omega),
      Finset.sum_image fun _ _ _ _ h => hinj h, Finset.sum_image fun _ _ _ _ h => hinj (mul_left_cancel₀ (by omega) h), ← Finset.mul_sum]
    simpa using Nat.mod_add_div t p

/-- The subset sums of a disjoint union are the sums of a subset sum of each part. -/
@[category API, AMS 11]
private lemma image_sum_powerset_union {s t : Finset ℕ} (h : Disjoint s t) :
    (s ∪ t).powerset.image (fun u => ∑ x ∈ u, x) =
      Finset.image₂ (· + ·) (s.powerset.image fun u => ∑ x ∈ u, x)
        (t.powerset.image fun u => ∑ x ∈ u, x) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_image₂]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, ⟨u ∩ s, Finset.inter_subset_right, rfl⟩, _,
      ⟨u ∩ t, Finset.inter_subset_right, rfl⟩, ?_⟩
    rw [← Finset.sum_union (h.mono Finset.inter_subset_right Finset.inter_subset_right),
      ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu]
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u ∪ v, Finset.union_subset_union hu hv, Finset.sum_union (h.mono hu hv)⟩

/--
Is the converse true, i.e., if $a(n) = n$, is $n$ necessarily an even perfect number?
- _Michael Engling_, Jul 20 2011

The answer is no: for example, $n = 492 = 2^2 \cdot 3 \cdot 41$ and
$n = 1652 = 2^2 \cdot 7 \cdot 59$ satisfy $a(n) = n$ but are abundant rather than perfect.
-/
@[category research solved, question, AMS 11]
theorem conjecture : ¬ ∀ n : ℕ, 0 < n → a n = n → n.Perfect ∧ Even n := by
  intro h
  -- `n = 492` has `a 492 = 492`, but its proper divisors sum to `684`. The subset sums of the
  -- proper divisors of `492` are the numbers `i + 41 * j` with `i < 29` and `j < 17`.
  have hdiv : Nat.properDivisors 492 = {1, 2, 3, 4, 6, 12} ∪ {41, 82, 123, 164, 246} := by
    decide +kernel
  have hdisj : Disjoint ({1, 2, 3, 4, 6, 12} : Finset ℕ) {41, 82, 123, 164, 246} := by decide
  have h1 : ({1, 2, 3, 4, 6, 12} : Finset ℕ).powerset.image (fun u => ∑ x ∈ u, x) =
      Finset.range 29 := by decide +kernel
  have h2 : ({41, 82, 123, 164, 246} : Finset ℕ).powerset.image (fun u => ∑ x ∈ u, x) =
      (Finset.range 17).image (41 * ·) := by decide +kernel
  have hinj : (Finset.range 29 ×ˢ Finset.range 17 : Set (ℕ × ℕ)).InjOn
      fun p => p.1 + 41 * p.2 := by
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hij hij'
    simp only [Prod.mk.injEq]
    dsimp only at h
    omega
  have h492 : a 492 = 492 := by
    rw [a, hdiv, image_sum_powerset_union hdisj, h1, h2, Finset.image₂_image_right,
      Finset.card_image₂_iff.mpr hinj, Finset.card_range, Finset.card_range]
  have hperf := (h 492 (by norm_num) h492).1
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)] at hperf
  revert hperf
  decide +kernel

end OeisA193279
