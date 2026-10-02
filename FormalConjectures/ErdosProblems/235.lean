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
# Erdős Problem 235

Let `N_k = 2 · 3 ⋯ p_k` be the product of the first `k` primes and let
`a_1 < a_2 < ⋯ < a_{φ(N_k)}` be the integers in `[0, N_k)` coprime to `N_k`.
Erdős asked whether, for every `c ≥ 0`, the limit

  `lim_{k → ∞} #{2 ≤ i ≤ φ(N_k) : a_i - a_{i-1} ≤ c N_k / φ(N_k)} / φ(N_k)`

exists and is a continuous function of `c`.  This was proved by Hooley (1965), with limit
`1 - e^{-c}`.  This file contains a complete, self-contained proof:

* `Erdos235.erdos_235` : the proportion tends to `1 - exp (-c)` for every `c ≥ 0`;
* `Erdos235.erdos_235_continuous` : the limit exists and is continuous in `c`.

## Proof outline

* `W(h)` = number of `x mod N_k` such that none of `x, …, x + h - 1` is coprime to `N_k`.
  Via the Chinese remainder theorem this is a count over `∏ ZMod p`.  Splitting the primes
  into small (`p ≤ h`) and large (`p > h`) ones, inclusion–exclusion for the large primes and
  a second-moment (variance) bound for the small primes, combined with Mertens-type product
  estimates, give the key estimate `W(h)/N_k ≈ exp(-c)` when `h φ(N_k)/N_k ≈ c`
  (`key_estimate`, `tendsto_cntW`).
* `E(h) = W(h) - W(h+1)` counts units `x` such that `x+1, …, x+h` are non-units; it
  differs by at most one from the number of gaps exceeding `h` (`Bk_le_EZ`, `EZ_le_Bk`).
* A summation-by-parts sandwich (`sandwich`) turns the asymptotics of `W` into those of `E`
  (`tendsto_EZ`), from which the main theorem follows.
-/

@[expose] public section


section Part1

open Finset

open scoped Classical

namespace Erdos235

section Counting

variable {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, NeZero (a i)]

/-- `Good a x j` : every coordinate of `x + j` is nonzero. -/
def Good (x : ∀ i, ZMod (a i)) (j : ℕ) : Prop := ∀ i, x i + (j : ZMod (a i)) ≠ 0

lemma card_filter_ne (n : ℕ) [NeZero n] (T : Finset ℕ) :
    #{b : ZMod n | ∀ j ∈ T, b + (j : ZMod n) ≠ 0} = n - #(T.image (fun j : ℕ => (j : ZMod n))) := by
  have : ({b : ZMod n | ∀ j ∈ T, b + (j : ZMod n) ≠ 0} : Finset (ZMod n)) =
      univ \ (T.image (fun j : ℕ => (j : ZMod n))).image Neg.neg := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_image, not_exists, not_and]
    constructor
    · rintro hb _ ⟨j, hj, rfl⟩ hneg
      exact hb j hj (by rw [← hneg]; ring)
    · intro hb j hj hzero
      exact hb (j : ZMod n) ⟨j, hj, rfl⟩ (eq_neg_of_add_eq_zero_left hzero).symm
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card,
    card_image_of_injective _ neg_injective]

/-- Chinese-remainder style count. -/
lemma card_forall_good (T : Finset ℕ) :
    #{x : ∀ i, ZMod (a i) | ∀ j ∈ T, Good a x j} =
      ∏ i, (a i - #(T.image (fun j : ℕ => (j : ZMod (a i))))) := by
  have : ({x : ∀ i, ZMod (a i) | ∀ j ∈ T, Good a x j} : Finset _) =
      Fintype.piFinset (fun i => ({b : ZMod (a i) | ∀ j ∈ T, b + (j : ZMod (a i)) ≠ 0} :
        Finset (ZMod (a i)))) := by
    ext x
    simp only [Good, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact ⟨fun h i j hj => h j hj i, fun h j hj i => h i j hj⟩
  rw [this, Fintype.card_piFinset]
  exact prod_congr rfl fun i _ => card_filter_ne (a i) T

/-- Number of `x` such that none of `x, x+1, …, x+h-1` is good. -/
noncomputable def cntW (h : ℕ) : ℕ := #{x : ∀ i, ZMod (a i) | ∀ j ∈ range h, ¬ Good a x j}

/-- Number of `x` such that `x + j` is not good for every `j ∈ A`. -/
noncomputable def cntV (A : Finset ℕ) : ℕ := #{x : ∀ i, ZMod (a i) | ∀ j ∈ A, ¬ Good a x j}

lemma cntW_split (Q : ι → Prop) (h : ℕ) :
    cntW a h = ∑ x₁ : (∀ i : {i // Q i}, ZMod (a i)),
      cntV (fun i : {i // ¬ Q i} => a i)
        ((range h).filter (Good (fun i : {i // Q i} => a i) x₁)) := by
  let e := Equiv.piEquivPiSubtypeProd Q (fun i => ZMod (a i))
  have hgood : ∀ x j, Good a x j ↔
      Good (fun i : {i // Q i} => a i) (e x).1 j ∧ Good (fun i : {i // ¬ Q i} => a i) (e x).2 j := by
    intro x j
    simp only [Good, e, Equiv.piEquivPiSubtypeProd_apply]
    constructor
    · intro h
      exact ⟨fun i => h i, fun i => h i⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hq : Q i
      · exact h1 ⟨i, hq⟩
      · exact h2 ⟨i, hq⟩
  unfold cntW cntV
  simp only [card_filter]
  rw [Fintype.sum_equiv e _ (fun y => if ∀ j ∈ range h,
      ¬ (Good (fun i : {i // Q i} => a i) y.1 j ∧ Good (fun i : {i // ¬ Q i} => a i) y.2 j)
      then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun x₂ _ => ?_
    congr 1
    apply propext
    simp only [mem_filter, mem_range]
    constructor
    · intro h j ⟨hj, h1⟩ h2
      exact h j hj ⟨h1, h2⟩
    · intro h j hj ⟨h1, h2⟩
      exact h j ⟨hj, h1⟩ h2
  · intro x
    simp only [hgood]

lemma card_image_natCast_of_lt (n : ℕ) (T : Finset ℕ) (hT : ∀ j ∈ T, j < n) :
    #(T.image (fun j : ℕ => (j : ZMod n))) = #T := by
  apply card_image_of_injOn
  intro j hj j' hj' hjj'
  simp only at hjj'
  rw [ZMod.natCast_eq_natCast_iff'] at hjj'
  rwa [Nat.mod_eq_of_lt (hT j hj), Nat.mod_eq_of_lt (hT j' hj')] at hjj'

/-- Inclusion–exclusion for `cntV` when all moduli exceed the shifts. -/
lemma cntV_eq_sum (A : Finset ℕ) (hA : ∀ j ∈ A, ∀ i, j < a i) :
    (cntV a A : ℝ) = ∑ t ∈ range (#A + 1),
      (-1 : ℝ) ^ t * ((#A).choose t : ℝ) * ∏ i, ((a i : ℝ) - t) := by
  classical
  set g : (∀ i, ZMod (a i)) → ℕ → ℝ := fun x j => if Good a x j then 1 else 0 with hg
  have h1 : (cntV a A : ℝ) = ∑ x, ∏ j ∈ A, (-g x j + 1) := by
    unfold cntV
    rw [card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← prod_boole]
    push_cast
    refine prod_congr rfl fun j _ => ?_
    by_cases hj : Good a x j <;> simp [hg, hj]
  have h2 : ∀ x, ∏ j ∈ A, (-g x j + 1) =
      ∑ T ∈ A.powerset, (-1 : ℝ) ^ #T * (if ∀ j ∈ T, Good a x j then 1 else 0) := by
    intro x
    rw [prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [prod_const_one, mul_one, ← prod_boole]
    rw [show (∏ j ∈ T, -g x j) = ∏ j ∈ T, ((-1 : ℝ) * g x j) by
      exact prod_congr rfl fun j _ => by ring]
    rw [prod_mul_distrib, prod_const]
  have h3 : ∀ T ∈ A.powerset, ∑ x : (∀ i, ZMod (a i)),
      (if ∀ j ∈ T, Good a x j then (1 : ℝ) else 0) = ∏ i, ((a i : ℝ) - #T) := by
    intro T hT
    rw [sum_boole, card_forall_good]
    push_cast
    refine prod_congr rfl fun i _ => ?_
    have hTi : ∀ j ∈ T, j < a i := fun j hj => hA j (mem_powerset.1 hT hj) i
    rw [card_image_natCast_of_lt _ _ hTi]
    have : #T ≤ a i := by
      calc #T ≤ #(range (a i)) := card_le_card (fun j hj => mem_range.2 (hTi j hj))
        _ = a i := card_range _
    push_cast [this]
    ring
  rw [h1]
  simp_rw [h2]
  rw [sum_comm]
  rw [show ∑ T ∈ A.powerset, ∑ x : (∀ i, ZMod (a i)),
      (-1 : ℝ) ^ #T * (if ∀ j ∈ T, Good a x j then 1 else 0) =
      ∑ T ∈ A.powerset, (-1 : ℝ) ^ #T * ∏ i, ((a i : ℝ) - #T) from
    Finset.sum_congr rfl fun T hT => by rw [← mul_sum, h3 T hT]]
  rw [sum_powerset_apply_card (fun m => (-1 : ℝ) ^ m * ∏ i, ((a i : ℝ) - m))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [nsmul_eq_mul]
  ring

end Counting

end Erdos235

end Part1


section Part2

open Finset

namespace Erdos235

section RealLemmas

lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hP1 : ∏ i ∈ s, (1 - x i) ≤ 1 :=
      prod_le_one (fun i hi => by linarith [h1 i (mem_insert_of_mem hi)])
        (fun i hi => by linarith [h0 i (mem_insert_of_mem hi)])
    have hxj0 := h0 j (mem_insert_self j s)
    nlinarith

lemma sum_inv_sq_Ioc_le (h : ℕ) (hh : 1 ≤ h) (K : ℕ) (hK : h ≤ K) :
    ∑ n ∈ Ioc h K, 1 / (n : ℝ) ^ 2 ≤ 1 / (h : ℝ) - 1 / (K : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [sum_Ioc_succ_top hK]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hh.trans hK
    have : 1 / ((K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- For distinct naturals all exceeding `h ≥ 1`, `∑ 1/a_i^2 ≤ 1/h`. -/
lemma sum_inv_sq_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a)
    (h : ℕ) (hh : 1 ≤ h) (hlt : ∀ i, h < a i) :
    ∑ i, 1 / (a i : ℝ) ^ 2 ≤ 1 / (h : ℝ) := by
  classical
  have h1 : ∑ i, 1 / (a i : ℝ) ^ 2 = ∑ n ∈ univ.image a, 1 / (n : ℝ) ^ 2 :=
    (sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (fun i _ j _ hij => ha hij)).symm
  have hsub : univ.image a ⊆ Ioc h (h + univ.sup a) := by
    intro n hn
    obtain ⟨i, -, rfl⟩ := mem_image.1 hn
    exact mem_Ioc.2 ⟨hlt i, le_add_left (le_sup (mem_univ i))⟩
  rw [h1]
  calc ∑ n ∈ univ.image a, 1 / (n : ℝ) ^ 2 ≤ ∑ n ∈ Ioc h (h + univ.sup a), 1 / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / (h : ℝ) - 1 / ((h + univ.sup a : ℕ) : ℝ) := sum_inv_sq_Ioc_le h hh _ (le_add_right le_rfl)
    _ ≤ 1 / (h : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((h + univ.sup a : ℕ) : ℝ) := by positivity
        linarith

lemma one_sub_div_le_pow (A : ℝ) (hA : 1 ≤ A) (t : ℕ) :
    1 - t / A ≤ (1 - 1 / A) ^ t := by
  have h := one_add_mul_le_pow (a := -(1 / A)) (by
    have : 1 / A ≤ 1 := by rw [div_le_one (by linarith)]; exact hA
    linarith) t
  convert h using 1
  ring

lemma pow_mul_le_one_sub_div (A : ℝ) (hA : 1 ≤ A) (t : ℕ) (ht : (t : ℝ) ≤ A) :
    (1 - 1 / A) ^ t * (1 - (t : ℝ) ^ 2 / A ^ 2) ≤ 1 - t / A := by
  have hA0 : 0 < A := by linarith
  have h0 : 0 ≤ 1 - 1 / A := by
    have : 1 / A ≤ 1 := by rw [div_le_one hA0]; exact hA
    linarith
  have h1 : (1 - 1 / A) ^ t ≤ Real.exp (-(t / A)) := by
    calc (1 - 1 / A) ^ t ≤ (Real.exp (-(1 / A))) ^ t := by
          apply pow_le_pow_left₀ h0
          linarith [Real.add_one_le_exp (-(1 / A))]
      _ = Real.exp (-(t / A)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : 1 + t / A ≤ Real.exp (t / A) := by linarith [Real.add_one_le_exp (t / A)]
  have h3 : (1 - 1 / A) ^ t * (1 + t / A) ≤ 1 := by
    calc (1 - 1 / A) ^ t * (1 + t / A) ≤ Real.exp (-(t / A)) * Real.exp (t / A) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 ≤ 1 - t / A := by
    rw [sub_nonneg, div_le_one hA0]; exact ht
  have : (1 - 1 / A) ^ t * (1 - (t : ℝ) ^ 2 / A ^ 2) =
      ((1 - 1 / A) ^ t * (1 + t / A)) * (1 - t / A) := by
    field_simp
    ring
  rw [this]
  nlinarith

/-- Comparison of `∏ (1 - t/a_i)` with `λ^t`. -/
lemma prod_one_sub_bounds {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) (t : ℕ)
    (ht : ∀ i, (t : ℝ) ≤ a i) :
    0 ≤ ∏ i, (1 - t / a i) ∧ ∏ i, (1 - t / a i) ≤ (∏ i, (1 - 1 / a i)) ^ t ∧
      (∏ i, (1 - 1 / a i)) ^ t - ∏ i, (1 - t / a i) ≤
        (∏ i, (1 - 1 / a i)) ^ t * ((t : ℝ) ^ 2 * ∑ i, 1 / (a i) ^ 2) := by
  have hpos : ∀ i, 0 < a i := fun i => by linarith [ha i]
  have hβ0 : ∀ i, 0 ≤ 1 - t / a i := fun i => by
    rw [sub_nonneg, div_le_one (hpos i)]; exact ht i
  have hα0 : ∀ i, 0 ≤ 1 - 1 / a i := fun i => by
    rw [sub_nonneg, div_le_one (hpos i)]; exact ha i
  refine ⟨prod_nonneg fun i _ => hβ0 i, ?_, ?_⟩
  · rw [← prod_pow]
    exact prod_le_prod (fun i _ => hβ0 i) (fun i _ => one_sub_div_le_pow _ (ha i) t)
  · have hlow : (∏ i, (1 - 1 / a i)) ^ t * ∏ i, (1 - (t : ℝ) ^ 2 / a i ^ 2) ≤
        ∏ i, (1 - t / a i) := by
      rw [← prod_pow, ← prod_mul_distrib]
      refine prod_le_prod (fun i _ => ?_) (fun i _ => pow_mul_le_one_sub_div _ (ha i) t (ht i))
      apply mul_nonneg (pow_nonneg (hα0 i) _)
      rw [sub_nonneg, div_le_one (pow_pos (hpos i) 2)]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ht i) 2
    have hsum : 1 - ∑ i, (t : ℝ) ^ 2 / a i ^ 2 ≤ ∏ i, (1 - (t : ℝ) ^ 2 / a i ^ 2) :=
      one_sub_sum_le_prod_one_sub _ _ (fun i _ => by positivity) (fun i _ => by
        rw [div_le_one (pow_pos (hpos i) 2)]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ht i) 2)
    have hlam0' : 0 ≤ (∏ i, (1 - 1 / a i)) ^ t := pow_nonneg (prod_nonneg fun i _ => hα0 i) _
    have : (t : ℝ) ^ 2 * ∑ i, 1 / (a i) ^ 2 = ∑ i, (t : ℝ) ^ 2 / a i ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hsum hlam0']

lemma sq_le_two_mul_two_pow (t : ℕ) : t ^ 2 ≤ 2 * 2 ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h | h
    · interval_cases n <;> simp
    · rw [pow_succ 2 n]; nlinarith

/-- Bound for the `L`-part of the sieve. -/
lemma Lpart_bound {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a) (h : ℕ)
    (hh : 1 ≤ h) (hlt : ∀ i, h < a i) (s : ℕ) (hs : s ≤ h) :
    |∑ t ∈ range (s + 1), (-1 : ℝ) ^ t * (s.choose t : ℝ) * ∏ i, (1 - (t : ℝ) / a i) -
        (1 - ∏ i, (1 - 1 / (a i : ℝ))) ^ s| ≤
      2 * (1 + 2 * ∏ i, (1 - 1 / (a i : ℝ))) ^ s / h := by
  set lam := ∏ i, (1 - 1 / (a i : ℝ)) with hlam
  have ha1 : ∀ i, (1 : ℝ) ≤ a i := fun i => by exact_mod_cast (Nat.one_le_iff_ne_zero.2
    (by have := hlt i; omega))
  have hlam0 : 0 ≤ lam := prod_nonneg fun i _ => by
    rw [sub_nonneg, div_le_one (by linarith [ha1 i])]; exact ha1 i
  have hσ : ∑ i, 1 / (a i : ℝ) ^ 2 ≤ 1 / (h : ℝ) := sum_inv_sq_le a ha h hh hlt
  have hσ0 : 0 ≤ ∑ i, 1 / (a i : ℝ) ^ 2 := sum_nonneg fun i _ => by positivity
  have hbinom : (1 - lam) ^ s = ∑ t ∈ range (s + 1), (-1 : ℝ) ^ t * (s.choose t : ℝ) * lam ^ t := by
    rw [show 1 - lam = -lam + 1 by ring, add_pow]
    exact sum_congr rfl fun t _ => by rw [one_pow, mul_one, neg_pow]; ring
  have hbinom2 : (1 + 2 * lam) ^ s = ∑ t ∈ range (s + 1), (2 * lam) ^ t * (s.choose t : ℝ) := by
    rw [add_comm, add_pow]
    exact sum_congr rfl fun t _ => by rw [one_pow, mul_one]
  rw [hbinom, ← sum_sub_distrib]
  calc |∑ t ∈ range (s + 1), ((-1 : ℝ) ^ t * (s.choose t : ℝ) * ∏ i, (1 - (t : ℝ) / a i) -
          (-1 : ℝ) ^ t * (s.choose t : ℝ) * lam ^ t)|
      ≤ ∑ t ∈ range (s + 1), |(-1 : ℝ) ^ t * (s.choose t : ℝ) * ∏ i, (1 - (t : ℝ) / a i) -
          (-1 : ℝ) ^ t * (s.choose t : ℝ) * lam ^ t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ range (s + 1), (s.choose t : ℝ) * (lam ^ t * (2 * 2 ^ t) * (1 / h)) := by
        refine sum_le_sum fun t ht => ?_
        have hts : t ≤ s := Nat.lt_succ_iff.1 (mem_range.1 ht)
        have htA : ∀ i, (t : ℝ) ≤ a i := fun i => by
          exact_mod_cast (hts.trans hs).trans (hlt i).le
        obtain ⟨_, hle, hdiff⟩ := prod_one_sub_bounds (fun i => (a i : ℝ)) ha1 t htA
        rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          Nat.abs_cast]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        refine hdiff.trans ?_
        show lam ^ t * _ ≤ _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam0 _)
        have ht2 : ((t : ℝ)) ^ 2 ≤ 2 * 2 ^ t := by exact_mod_cast sq_le_two_mul_two_pow t
        exact mul_le_mul ht2 hσ hσ0 (by positivity)
    _ = 2 * (1 + 2 * lam) ^ s / h := by
        rw [hbinom2, mul_sum, sum_div]
        exact sum_congr rfl fun t _ => by rw [mul_pow]; ring

lemma abs_one_sub_pow_sub_exp_le (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (s : ℕ) :
    |(1 - lam) ^ s - Real.exp (-(s * lam))| ≤ s * lam ^ 2 := by
  have hb : Real.exp (-(s * lam)) = Real.exp (-lam) ^ s := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hb]
  refine (abs_pow_sub_pow_le _ _ _).trans ?_
  have hmax : max |1 - lam| |Real.exp (-lam)| ≤ 1 := by
    apply max_le
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by linarith)
  have hd : |1 - lam - Real.exp (-lam)| ≤ lam ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -lam) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
    have e1 : 1 - lam - Real.exp (-lam) = -(Real.exp (-lam) - 1 - -lam) := by ring
    rw [e1, abs_neg]; rwa [neg_sq] at this
  calc |1 - lam - Real.exp (-lam)| * s * max |1 - lam| |Real.exp (-lam)| ^ (s - 1)
      ≤ lam ^ 2 * s * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _))
          (pow_le_one₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax) (by positivity)
          (by positivity)
    _ = s * lam ^ 2 := by ring

lemma exp_neg_sub_exp_neg_le (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have h1 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h1]
  have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by linarith [Real.add_one_le_exp (-(v - u))]
  have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 : 0 < Real.exp (-u) := Real.exp_pos _
  nlinarith

lemma abs_exp_neg_sub_exp_neg_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 (neg_le_neg h)]), abs_sub_comm,
      abs_of_nonneg (by linarith)]
    exact exp_neg_sub_exp_neg_le u v hu h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.2 (neg_le_neg h)]),
      abs_of_nonneg (by linarith)]
    exact exp_neg_sub_exp_neg_le v u hv h

/-- Pointwise estimate used in the averaging argument. -/
lemma pointwise_bound (E lam c δ μ : ℝ) (s h : ℕ) (hh : 1 ≤ h) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hμ : |μ * lam - c| ≤ δ / 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE : |E - (1 - lam) ^ s| ≤ 2 * (1 + 2 * lam) ^ s / h) :
    |E - Real.exp (-c)| ≤
      2 * Real.exp (2 * (c + 1)) / h + (c + 1) * lam + δ + 4 * lam ^ 2 * (s - μ) ^ 2 / δ ^ 2 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hrest : 0 ≤ 4 * lam ^ 2 * (s - μ) ^ 2 / δ ^ 2 := by positivity
  have hexpc0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hexpc1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  by_cases hgood : |s * lam - c| ≤ δ
  · have hsl : (s : ℝ) * lam ≤ c + 1 := by
      have := (abs_le.1 hgood).2; linarith
    have hsl0 : 0 ≤ (s : ℝ) * lam := by positivity
    have h1 : 2 * (1 + 2 * lam) ^ s / h ≤ 2 * Real.exp (2 * (c + 1)) / h := by
      apply div_le_div_of_nonneg_right _ hh'.le
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc (1 + 2 * lam) ^ s ≤ Real.exp (2 * lam) ^ s := by
            apply pow_le_pow_left₀ (by positivity)
            linarith [Real.add_one_le_exp (2 * lam)]
        _ = Real.exp (2 * (s * lam)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (2 * (c + 1)) := Real.exp_le_exp.2 (by linarith)
    have h2 := abs_one_sub_pow_sub_exp_le lam hlam0 hlam1 s
    have h2' : (s : ℝ) * lam ^ 2 ≤ (c + 1) * lam := by
      have : (s : ℝ) * lam ^ 2 = (s * lam) * lam := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hsl hlam0
    have h3 := abs_exp_neg_sub_exp_neg_le (s * lam) c hsl0 hc.le
    have t1 := abs_sub_le E ((1 - lam) ^ s) (Real.exp (-c))
    have t2 := abs_sub_le ((1 - lam) ^ s) (Real.exp (-(s * lam))) (Real.exp (-c))
    linarith
  · push_neg at hgood
    have h1 : |E - Real.exp (-c)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : δ / 2 < |((s : ℝ) - μ) * lam| := by
      have : |(s : ℝ) * lam - c| ≤ |((s : ℝ) - μ) * lam| + |μ * lam - c| := by
        have := abs_add_le (((s : ℝ) - μ) * lam) (μ * lam - c)
        convert this using 2; ring
      linarith
    have h3 : δ ^ 2 / 4 < lam ^ 2 * ((s : ℝ) - μ) ^ 2 := by
      have h4 : (δ / 2) ^ 2 < |((s : ℝ) - μ) * lam| ^ 2 :=
        pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      rw [sq_abs] at h4
      nlinarith
    have h5 : 1 ≤ 4 * lam ^ 2 * ((s : ℝ) - μ) ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ 2 * Real.exp (2 * (c + 1)) / h := by positivity
    have : 0 ≤ (c + 1) * lam := by positivity
    linarith

end RealLemmas

end Erdos235

end Part2


section Part3

open Finset

open scoped Classical

namespace Erdos235

lemma abs_card_modEq_sub_le (h m j : ℕ) (hm : 0 < m) :
    |(#{j' ∈ range h | j' ≡ j [MOD m]} : ℝ) - h / m| ≤ 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card h hm j]
  have h1 : ((h / m : ℕ) : ℝ) ≤ (h : ℝ) / m := Nat.cast_div_le
  have h2 : (h : ℝ) / m < ((h / m : ℕ) : ℝ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ) h m]; exact Nat.lt_floor_add_one _
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

lemma modEq_forall_iff_prod {ι : Type*} (T : Finset ι) (p : ι → ℕ)
    (hcop : ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Nat.Coprime (p i) (p i')) (x y : ℕ) :
    (∀ i ∈ T, x ≡ y [MOD p i]) ↔ x ≡ y [MOD ∏ i ∈ T, p i] := by
  simp only [Nat.modEq_iff_dvd]
  push_cast
  constructor
  · intro h
    exact Finset.prod_dvd_of_coprime
      (fun i hi i' hi' hne => Nat.isCoprime_iff_coprime.2 (hcop i hi i' hi' hne)) h
  · intro h i hi
    exact dvd_trans (dvd_prod_of_mem (fun i => (p i : ℤ)) hi) h

section Sieve

variable {ι : Type*}

/-- The key cancellation: for nonempty `T`, the sum over `j' < h` of
`∏_{i ∈ T} (a_i [j' ≡ j mod a_i] - 1)` is bounded by `∏_{i ∈ T} (a_i + 1)`. -/
lemma abs_sum_prod_indicator_le (a : ι → ℕ) (ha : Function.Injective a)
    (hp : ∀ i, (a i).Prime) (j h : ℕ) (T : Finset ι) (hT : T.Nonempty) :
    |∑ j' ∈ range h, ∏ i ∈ T, ((a i : ℝ) * (if j' ≡ j [MOD a i] then 1 else 0) + (-1))| ≤
      ∏ i ∈ T, ((a i : ℝ) + 1) := by
  have hcop : ∀ E : Finset ι, ∀ i ∈ E, ∀ i' ∈ E, i ≠ i' → Nat.Coprime (a i) (a i') :=
    fun E i _ i' _ hne => (Nat.coprime_primes (hp i) (hp i')).2 (fun h => hne (ha h))
  have hPpos : ∀ E : Finset ι, (0 : ℝ) < ∏ i ∈ E, (a i : ℝ) :=
    fun E => prod_pos fun i _ => by exact_mod_cast (hp i).pos
  -- expand the product
  have hexp : ∀ j', ∏ i ∈ T, ((a i : ℝ) * (if j' ≡ j [MOD a i] then 1 else 0) + (-1)) =
      ∑ E ∈ T.powerset, (-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
        (if j' ≡ j [MOD ∏ i ∈ E, a i] then 1 else 0)) := by
    intro j'
    rw [prod_add]
    refine sum_congr rfl fun E hE => ?_
    rw [prod_const, prod_mul_distrib, prod_boole]
    have : (∀ i ∈ E, j' ≡ j [MOD a i]) ↔ j' ≡ j [MOD ∏ i ∈ E, a i] :=
      modEq_forall_iff_prod E a (hcop E) j' j
    simp only [this]
    ring
  simp_rw [hexp]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have hcount : ∀ E : Finset ι, ∑ j' ∈ range h,
      (if j' ≡ j [MOD ∏ i ∈ E, a i] then (1 : ℝ) else 0) =
        (#{j' ∈ range h | j' ≡ j [MOD ∏ i ∈ E, a i]} : ℝ) := by
    intro E; rw [sum_boole]
  simp_rw [hcount]
  -- the main terms cancel
  have hzero : ∑ E ∈ T.powerset, (-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
      ((h : ℝ) / ∏ i ∈ E, (a i : ℝ))) = 0 := by
    have : ∀ E ∈ T.powerset, (-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
        ((h : ℝ) / ∏ i ∈ E, (a i : ℝ))) = h * ((∏ i ∈ E, (1 : ℝ)) * ∏ i ∈ T \ E, (-1 : ℝ)) := by
      intro E _
      rw [prod_const_one, prod_const, mul_div_cancel₀ _ (hPpos E).ne']
      ring
    rw [sum_congr rfl this, ← mul_sum, ← prod_add]
    obtain ⟨i₀, hi₀⟩ := hT
    rw [prod_eq_zero hi₀ (by ring), mul_zero]
  have hsplit : ∑ E ∈ T.powerset, (-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
      (#{j' ∈ range h | j' ≡ j [MOD ∏ i ∈ E, a i]} : ℝ)) =
      ∑ E ∈ T.powerset, (-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
        ((#{j' ∈ range h | j' ≡ j [MOD ∏ i ∈ E, a i]} : ℝ) - (h : ℝ) / ∏ i ∈ E, (a i : ℝ))) := by
    rw [← sub_zero (∑ E ∈ T.powerset, _), ← hzero, ← sum_sub_distrib]
    exact sum_congr rfl fun E _ => by ring
  rw [hsplit]
  calc _ ≤ ∑ E ∈ T.powerset, |(-1 : ℝ) ^ #(T \ E) * ((∏ i ∈ E, (a i : ℝ)) *
        ((#{j' ∈ range h | j' ≡ j [MOD ∏ i ∈ E, a i]} : ℝ) - (h : ℝ) / ∏ i ∈ E, (a i : ℝ)))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ E ∈ T.powerset, (∏ i ∈ E, (a i : ℝ)) * ∏ i ∈ T \ E, (1 : ℝ) := by
        refine sum_le_sum fun E _ => ?_
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
          abs_of_pos (hPpos E), prod_const_one, mul_one]
        have := abs_card_modEq_sub_le h (∏ i ∈ E, a i) j
          (prod_pos fun i _ => (hp i).pos)
        push_cast at this
        exact mul_le_of_le_one_right (hPpos E).le this
    _ = ∏ i ∈ T, ((a i : ℝ) + 1) := (prod_add _ _ _).symm

/-- The normalized pair correlation ("singular series") of the reduced residues. -/
noncomputable def sing [Fintype ι] (a : ι → ℕ) (j j' : ℕ) : ℝ :=
  ∏ i, (1 + ((a i : ℝ) * (if j' ≡ j [MOD a i] then 1 else 0) - 1) / ((a i : ℝ) - 1) ^ 2)

lemma abs_sum_sing_sub_one_le [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a)
    (hp : ∀ i, (a i).Prime) (j h : ℕ) :
    |∑ j' ∈ range h, (sing a j j' - 1)| ≤
      ∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) - 1 := by
  set c : Finset ι → ℝ := fun T => ∏ i ∈ T, (1 / ((a i : ℝ) - 1) ^ 2) with hc
  have hc0 : ∀ T, 0 ≤ c T := fun T => prod_nonneg fun i _ => by positivity
  have hexpand : ∀ (f : ι → ℝ), ∏ i, (1 + f i / ((a i : ℝ) - 1) ^ 2) - 1 =
      ∑ T ∈ (univ : Finset ι).powerset.erase ∅, c T * ∏ i ∈ T, f i := by
    intro f
    have : ∏ i, (1 + f i / ((a i : ℝ) - 1) ^ 2) =
        ∑ T ∈ (univ : Finset ι).powerset, c T * ∏ i ∈ T, f i := by
      rw [show (∏ i, (1 + f i / ((a i : ℝ) - 1) ^ 2)) =
          ∏ i, (1 / ((a i : ℝ) - 1) ^ 2 * f i + 1) from
        prod_congr rfl fun i _ => by ring, prod_add]
      exact sum_congr rfl fun T _ => by rw [prod_const_one, mul_one, prod_mul_distrib]
    rw [this, sum_erase_eq_sub (empty_mem_powerset _)]
    simp [hc]
  have h1 : ∀ j', sing a j j' - 1 = ∑ T ∈ (univ : Finset ι).powerset.erase ∅, c T *
      ∏ i ∈ T, ((a i : ℝ) * (if j' ≡ j [MOD a i] then 1 else 0) + (-1)) := by
    intro j'
    rw [sing, ← hexpand]
    simp only [sub_eq_add_neg]
  rw [hexpand (fun i => (a i : ℝ) + 1)]
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [← mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun T hT => ?_)
  rw [abs_mul, abs_of_nonneg (hc0 T)]
  apply mul_le_mul_of_nonneg_left _ (hc0 T)
  apply abs_sum_prod_indicator_le a ha hp j h T
  rw [nonempty_iff_ne_empty]
  exact ne_of_mem_erase hT

end Sieve

end Erdos235

namespace Erdos235

section Variance

variable {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, NeZero (a i)]

/-- Number of good shifts among `x, x+1, …, x+h-1`. -/
noncomputable def sCount (h : ℕ) (x : ∀ i, ZMod (a i)) : ℕ := #{j ∈ range h | Good a x j}

omit [Fintype ι] [∀ i, NeZero (a i)] in
lemma sCount_le (h : ℕ) (x : ∀ i, ZMod (a i)) : sCount a h x ≤ h :=
  (card_filter_le _ _).trans (card_range h).le

lemma card_pi_zmod : (Fintype.card (∀ i, ZMod (a i)) : ℝ) = ∏ i, (a i : ℝ) := by
  rw [Fintype.card_pi]; push_cast; simp [ZMod.card]

lemma sum_sCount (h : ℕ) :
    ∑ x : (∀ i, ZMod (a i)), (sCount a h x : ℝ) = h * ∏ i, ((a i : ℝ) - 1) := by
  simp only [sCount, card_filter]
  push_cast
  rw [sum_comm]
  have : ∀ j ∈ range h, ∑ x : (∀ i, ZMod (a i)), (if Good a x j then (1 : ℝ) else 0) =
      ∏ i, ((a i : ℝ) - 1) := by
    intro j _
    rw [sum_boole]
    have := card_forall_good a {j}
    simp only [mem_singleton, forall_eq, image_singleton, card_singleton] at this
    rw [this]
    push_cast [Nat.one_le_iff_ne_zero.2 (NeZero.ne _)]
    rfl
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

lemma sum_sCount_sq (h : ℕ) :
    ∑ x : (∀ i, ZMod (a i)), (sCount a h x : ℝ) ^ 2 =
      ∑ j ∈ range h, ∑ j' ∈ range h,
        ∏ i, ((a i : ℝ) - #(({j, j'} : Finset ℕ).image (fun t : ℕ => (t : ZMod (a i))))) := by
  simp only [sCount, card_filter]
  push_cast
  simp_rw [sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j' _ => ?_
  have hc := card_forall_good a {j, j'}
  have : ∀ x : (∀ i, ZMod (a i)), ((if Good a x j then (1 : ℝ) else 0) *
      if Good a x j' then 1 else 0) = if ∀ t ∈ ({j, j'} : Finset ℕ), Good a x t then 1 else 0 := by
    intro x
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    by_cases h1 : Good a x j <;> by_cases h2 : Good a x j' <;> simp [h1, h2]
  simp_rw [this]
  rw [sum_boole, hc]
  push_cast
  refine prod_congr rfl fun i _ => ?_
  have : #(({j, j'} : Finset ℕ).image (fun t : ℕ => (t : ZMod (a i)))) ≤ a i := by
    calc _ ≤ #(univ : Finset (ZMod (a i))) := card_le_card (subset_univ _)
      _ = a i := by rw [card_univ, ZMod.card]
  push_cast [this]
  rfl

lemma pair_factor (n : ℕ) [NeZero n] (hn : 2 ≤ n) (j j' : ℕ) :
    (n : ℝ) - #(({j, j'} : Finset ℕ).image (fun t : ℕ => (t : ZMod n))) =
      ((n : ℝ) - 1) ^ 2 / n * (1 + ((n : ℝ) * (if j' ≡ j [MOD n] then 1 else 0) - 1) /
        ((n : ℝ) - 1) ^ 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  rw [image_insert, image_singleton]
  by_cases hjj : j' ≡ j [MOD n]
  · have : (j : ZMod n) = j' := (ZMod.natCast_eq_natCast_iff _ _ _).2 hjj.symm
    rw [this, insert_eq_of_mem (mem_singleton_self _), card_singleton, if_pos hjj]
    field_simp
    ring
  · have : (j : ZMod n) ≠ j' := fun h => hjj ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm
    rw [card_pair this, if_neg hjj]
    field_simp
    ring

/-- Variance bound for the number of good shifts. -/
lemma sum_sCount_sub_sq_le (ha : Function.Injective a) (hp : ∀ i, (a i).Prime) (h : ℕ) :
    ∑ x : (∀ i, ZMod (a i)), ((sCount a h x : ℝ) - h * ∏ i, (1 - 1 / (a i : ℝ))) ^ 2 ≤
      (∏ i, (a i : ℝ)) * (∏ i, (1 - 1 / (a i : ℝ))) ^ 2 * h *
        (∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) - 1) := by
  set M := ∏ i, (a i : ℝ) with hM
  set D := ∏ i, ((a i : ℝ) - 1) with hD
  set ρ := ∏ i, (1 - 1 / (a i : ℝ)) with hρ
  have hapos : ∀ i, (0 : ℝ) < a i := fun i => by exact_mod_cast (hp i).pos
  have hMpos : 0 < M := prod_pos fun i _ => hapos i
  have hρD : ρ = D / M := by
    rw [hρ, hD, hM, ← prod_div_distrib]
    exact prod_congr rfl fun i _ => by field_simp [(hapos i).ne']
  have hsq : ∑ x : (∀ i, ZMod (a i)), (sCount a h x : ℝ) ^ 2 =
      D ^ 2 / M * ∑ j ∈ range h, ∑ j' ∈ range h, sing a j j' := by
    rw [sum_sCount_sq, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j' _ => ?_
    rw [sing, hD, hM, ← prod_pow, ← prod_div_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => pair_factor (a i) (hp i).two_le j j'
  have hexp : ∑ x : (∀ i, ZMod (a i)), ((sCount a h x : ℝ) - h * ρ) ^ 2 =
      ∑ x : (∀ i, ZMod (a i)), (sCount a h x : ℝ) ^ 2 -
        2 * (h * ρ) * ∑ x : (∀ i, ZMod (a i)), (sCount a h x : ℝ) + M * (h * ρ) ^ 2 := by
    have hcard : ((univ : Finset (∀ i, ZMod (a i))).card : ℝ) = M := by
      rw [card_univ, card_pi_zmod]
    have : ∑ x : (∀ i, ZMod (a i)), ((sCount a h x : ℝ) - h * ρ) ^ 2 =
        ∑ x : (∀ i, ZMod (a i)), ((sCount a h x : ℝ) ^ 2 - 2 * (h * ρ) * (sCount a h x : ℝ) +
          (h * ρ) ^ 2) := sum_congr rfl fun x _ => by ring
    rw [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hcard]
  have hmain : ∑ x : (∀ i, ZMod (a i)), ((sCount a h x : ℝ) - h * ρ) ^ 2 =
      D ^ 2 / M * ∑ j ∈ range h, ∑ j' ∈ range h, (sing a j j' - 1) := by
    rw [hexp, hsq, sum_sCount, hρD]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
    ring
  rw [hmain]
  have hB : ∑ j ∈ range h, ∑ j' ∈ range h, (sing a j j' - 1) ≤
      h * (∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) - 1) := by
    calc _ ≤ ∑ j ∈ range h, |∑ j' ∈ range h, (sing a j j' - 1)| :=
          sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ j ∈ range h, (∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) - 1) :=
          sum_le_sum fun j _ => abs_sum_sing_sub_one_le a ha hp j h
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hfac : M * ρ ^ 2 = D ^ 2 / M := by rw [hρD]; field_simp
  calc D ^ 2 / M * ∑ j ∈ range h, ∑ j' ∈ range h, (sing a j j' - 1)
      ≤ D ^ 2 / M * (h * (∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) - 1)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by rw [← hfac]; ring

end Variance

end Erdos235

end Part3


section Part4

open Finset

namespace Erdos235

section Mertens

/-- `∏_{p ≤ n} p/(p-1)`. -/
noncomputable def primeProd (n : ℕ) : ℝ := ∏ p ∈ (range (n + 1)).filter Nat.Prime, (p : ℝ) / (p - 1)

lemma primeProd_succ (n : ℕ) : primeProd (n + 1) =
    primeProd n * (if (n + 1).Prime then ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) - 1) else 1) := by
  unfold primeProd
  rw [range_add_one (n := n + 1), filter_insert]
  split_ifs with hp
  · rw [prod_insert (by simp), mul_comm]
  · rw [mul_one]

lemma primeProd_nonneg (n : ℕ) : 0 ≤ primeProd n :=
  prod_nonneg fun p hp => by
    have := (mem_filter.1 hp).2.one_lt
    have : (1 : ℝ) < p := by exact_mod_cast this
    exact div_nonneg (by linarith) (by linarith)

lemma primeProd_sq_le (n : ℕ) (hn : 1 ≤ n) : primeProd n ^ 2 ≤ 4 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h
    · subst h
      rw [show primeProd 1 = 1 by
        rw [primeProd, show (filter Nat.Prime (range 2)) = ∅ by decide, prod_empty]]
      norm_num
    · subst h
      rw [primeProd_succ]; norm_num [primeProd]
      rw [show (filter Nat.Prime (range 2)) = ∅ by decide]; norm_num
    · subst h
      rw [primeProd_succ, primeProd_succ]; norm_num [primeProd]
      rw [show (filter Nat.Prime (range 2)) = ∅ by decide]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rcases Nat.even_or_odd (m + 2) with he | ho
      · have hnp : ¬ (m + 2).Prime := fun hp => by
          have := (Nat.Prime.even_iff hp).1 he; omega
        rw [show m + 2 = (m + 1) + 1 from rfl, primeProd_succ, if_neg hnp, mul_one]
        have := ih (m + 1) (by omega) (by omega)
        push_cast at this ⊢; linarith
      · have he : Even (m + 1) := by
          rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩
        have hnp : ¬ (m + 1).Prime := fun hp => by
          have := (Nat.Prime.even_iff hp).1 he; omega
        rw [show m + 2 = (m + 1) + 1 from rfl, primeProd_succ, primeProd_succ, if_neg hnp,
          mul_one]
        have ihm := ih m (by omega) (by omega)
        have hQ := primeProd_nonneg m
        have hm : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
        have hf : (if (m + 1 + 1).Prime then ((m + 1 + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) - 1)
            else 1) ≤ ((m : ℝ) + 2) / (m + 1) := by
          split_ifs
          · push_cast; apply le_of_eq; ring
          · rw [le_div_iff₀ (by linarith)]; linarith
        have hf0 : 0 ≤ (if (m + 1 + 1).Prime then ((m + 1 + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) - 1)
            else 1) := by
          split_ifs
          · push_cast; apply div_nonneg <;> linarith
          · norm_num
        calc (primeProd m * (if (m + 1 + 1).Prime then ((m + 1 + 1 : ℕ) : ℝ) /
              ((m + 1 + 1 : ℕ) - 1) else 1)) ^ 2
            ≤ (primeProd m * (((m : ℝ) + 2) / (m + 1))) ^ 2 := by
              apply pow_le_pow_left₀ (mul_nonneg hQ hf0)
              exact mul_le_mul_of_nonneg_left hf hQ
          _ = primeProd m ^ 2 * (((m : ℝ) + 2) / (m + 1)) ^ 2 := by ring
          _ ≤ (4 * m) * (((m : ℝ) + 2) / (m + 1)) ^ 2 :=
              mul_le_mul_of_nonneg_right ihm (by positivity)
          _ ≤ 4 * ((m + 2 : ℕ) : ℝ) := by
              push_cast
              rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
              nlinarith

lemma prod_le_prod_of_subset_of_one_le_real {α : Type*} (s t : Finset α) (f : α → ℝ)
    (h : s ⊆ t) (h1 : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical
  rw [← prod_sdiff h]
  have h0 : 0 ≤ ∏ i ∈ s, f i := prod_nonneg fun i hi => by linarith [h1 i (h hi)]
  have h2 : 1 ≤ ∏ i ∈ t \ s, f i := by
    have := prod_le_prod (s := t \ s) (f := fun _ => (1 : ℝ)) (g := f) (fun _ _ => zero_le_one)
      (fun i hi => h1 i (mem_sdiff.1 hi).1)
    simpa using this
  nlinarith

/-- For distinct primes `a i ≤ n`, `(∏ a_i/(a_i - 1))^2 ≤ 4 n`. -/
lemma prod_div_sub_one_sq_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a)
    (hp : ∀ i, (a i).Prime) (n : ℕ) (hn : 1 ≤ n) (hle : ∀ i, a i ≤ n) :
    (∏ i, (a i : ℝ) / ((a i : ℝ) - 1)) ^ 2 ≤ 4 * n := by
  classical
  have h1 : ∏ i, (a i : ℝ) / ((a i : ℝ) - 1) =
      ∏ p ∈ univ.image a, (p : ℝ) / ((p : ℝ) - 1) :=
    (prod_image (f := fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1)) (fun i _ j _ hij => ha hij)).symm
  have hsub : univ.image a ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hp'
    exact mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hle i)), hp i⟩
  have h2 : ∏ i, (a i : ℝ) / ((a i : ℝ) - 1) ≤ primeProd n := by
    rw [h1]
    apply prod_le_prod_of_subset_of_one_le_real _ _ _ hsub
    intro p hp'
    have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp').2.one_lt
    rw [le_div_iff₀ (by linarith)]; linarith
  have h0 : 0 ≤ ∏ i, (a i : ℝ) / ((a i : ℝ) - 1) := prod_nonneg fun i _ => by
    have : (1 : ℝ) < a i := by exact_mod_cast (hp i).one_lt
    exact div_nonneg (by linarith) (by linarith)
  calc (∏ i, (a i : ℝ) / ((a i : ℝ) - 1)) ^ 2 ≤ primeProd n ^ 2 := pow_le_pow_left₀ h0 h2 2
    _ ≤ 4 * n := primeProd_sq_le n hn

lemma prod_Ioc_one_add_le (K : ℕ) (hK : 2 ≤ K) :
    ∏ n ∈ Ioc 1 K, (1 + 2 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 6 * ((K : ℝ) - 1) / ((K : ℝ) + 1) := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    rw [prod_Ioc_succ_top (by omega)]
    have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hpos : 0 ≤ ∏ n ∈ Ioc 1 K, (1 + 2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
      prod_nonneg fun n hn => by
        have : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
        have : 0 ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := div_nonneg (by norm_num)
          (mul_nonneg (by linarith) (by linarith))
        linarith
    have hf0 : 0 ≤ 1 + 2 / (((K + 1 : ℕ) : ℝ) * (((K + 1 : ℕ) : ℝ) - 1)) := by
      push_cast
      have : 0 ≤ 2 / (((K : ℝ) + 1) * ((K : ℝ) + 1 - 1)) := div_nonneg (by norm_num)
        (mul_nonneg (by linarith) (by linarith))
      linarith
    calc (∏ n ∈ Ioc 1 K, (1 + 2 / ((n : ℝ) * ((n : ℝ) - 1)))) *
          (1 + 2 / (((K + 1 : ℕ) : ℝ) * (((K + 1 : ℕ) : ℝ) - 1)))
        ≤ 6 * ((K : ℝ) - 1) / ((K : ℝ) + 1) *
          (1 + 2 / (((K + 1 : ℕ) : ℝ) * (((K + 1 : ℕ) : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_right ih hf0
      _ ≤ 6 * (((K + 1 : ℕ) : ℝ) - 1) / (((K + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [show (K : ℝ) + 1 - 1 = K by ring]
          have hK0 : (0 : ℝ) < K := by linarith
          rw [show 6 * ((K : ℝ) - 1) / (K + 1) * (1 + 2 / ((K + 1) * K)) =
              6 * ((K : ℝ) - 1) * (K ^ 2 + K + 2) / ((K + 1) ^ 2 * K) by
            field_simp]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have e : ((K : ℝ) - 1) * (K ^ 2 + K + 2) * (K + 2) = ((K : ℝ) ^ 2 + K) ^ 2 - 4 := by ring
          nlinarith [e]

lemma prod_one_add_two_div_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a)
    (h2 : ∀ i, 2 ≤ a i) :
    ∏ i, (1 + 2 / ((a i : ℝ) * ((a i : ℝ) - 1))) ≤ 6 := by
  classical
  have h1 : ∏ i, (1 + 2 / ((a i : ℝ) * ((a i : ℝ) - 1))) =
      ∏ p ∈ univ.image a, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) :=
    (prod_image (f := fun p : ℕ => 1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))
      (fun i _ j _ hij => ha hij)).symm
  have hsub : univ.image a ⊆ Ioc 1 (2 + univ.sup a) := by
    intro p hp'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hp'
    exact mem_Ioc.2 ⟨h2 i, le_add_left (le_sup (mem_univ i))⟩
  rw [h1]
  calc ∏ p ∈ univ.image a, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∏ n ∈ Ioc 1 (2 + univ.sup a), (1 + 2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        apply prod_le_prod_of_subset_of_one_le_real _ _ _ hsub
        intro n hn
        have : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
        have : 0 ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := div_nonneg (by norm_num)
          (mul_nonneg (by linarith) (by linarith))
        linarith
    _ ≤ 6 * (((2 + univ.sup a : ℕ) : ℝ) - 1) / (((2 + univ.sup a : ℕ) : ℝ) + 1) :=
        prod_Ioc_one_add_le _ (le_add_right le_rfl)
    _ ≤ 6 := by
        rw [div_le_iff₀ (by positivity)]
        linarith

/-- `B(S) ≤ 6 q(S)`. -/
lemma prod_B_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a)
    (h2 : ∀ i, 2 ≤ a i) :
    ∏ i, (1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2) ≤
      6 * ∏ i, (a i : ℝ) / ((a i : ℝ) - 1) := by
  have hfac : ∀ i, 1 + ((a i : ℝ) + 1) / ((a i : ℝ) - 1) ^ 2 =
      (a i : ℝ) / ((a i : ℝ) - 1) * (1 + 2 / ((a i : ℝ) * ((a i : ℝ) - 1))) := by
    intro i
    have : (2 : ℝ) ≤ a i := by exact_mod_cast h2 i
    have h1 : (a i : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (a i : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  simp_rw [hfac]
  rw [prod_mul_distrib, mul_comm 6]
  have hq0 : 0 ≤ ∏ i, (a i : ℝ) / ((a i : ℝ) - 1) := prod_nonneg fun i _ => by
    have : (2 : ℝ) ≤ a i := by exact_mod_cast h2 i
    exact div_nonneg (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left (prod_one_add_two_div_le a ha h2) hq0

end Mertens

end Erdos235

end Part4


section Part5

open Finset

open scoped Classical

namespace Erdos235

lemma prod_one_sub_inv_eq {ι : Type*} [Fintype ι] (a : ι → ℕ) (h2 : ∀ i, 2 ≤ a i) :
    ∏ i, (1 - 1 / (a i : ℝ)) = 1 / ∏ i, ((a i : ℝ) / ((a i : ℝ) - 1)) := by
  have hpos : 0 < ∏ i, ((a i : ℝ) / ((a i : ℝ) - 1)) := prod_pos fun i _ => by
    have : (2 : ℝ) ≤ a i := by exact_mod_cast h2 i
    exact div_pos (by linarith) (by linarith)
  rw [eq_div_iff hpos.ne', ← prod_mul_distrib]
  refine prod_eq_one fun i _ => ?_
  have : (2 : ℝ) ≤ a i := by exact_mod_cast h2 i
  have h1 : (a i : ℝ) ≠ 0 := by linarith
  have h3 : (a i : ℝ) - 1 ≠ 0 := by linarith
  field_simp

lemma final_numeric (c δ r hR lam X B : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hr1 : 1 ≤ r) (hrh : hR = r ^ 2) (hlam_le : lam ≤ 2 * (c + 1) / r)
    (hX0 : 0 ≤ X) (hX : X ≤ c + 1) (hB0 : 1 ≤ B) (hBr : B ≤ 12 * r) :
    2 * Real.exp (2 * (c + 1)) / hR + (c + 1) * lam + δ + 4 * X ^ 2 * (B - 1) / (hR * δ ^ 2) ≤
      δ + (2 * Real.exp (2 * (c + 1)) + 50 * (c + 1) ^ 2) / (δ ^ 2 * r) := by
  have hr0 : 0 < r := by linarith
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hδ2' : 0 < δ ^ 2 := by positivity
  have hE := Real.exp_pos (2 * (c + 1))
  subst hrh
  have hdr : δ ^ 2 * r ≤ r ^ 2 := by nlinarith
  have t1 : 2 * Real.exp (2 * (c + 1)) / r ^ 2 ≤ 2 * Real.exp (2 * (c + 1)) / (δ ^ 2 * r) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hdr
  have t2 : (c + 1) * lam ≤ 2 * (c + 1) ^ 2 / (δ ^ 2 * r) := by
    calc (c + 1) * lam ≤ (c + 1) * (2 * (c + 1) / r) :=
          mul_le_mul_of_nonneg_left hlam_le (by linarith)
      _ = 2 * (c + 1) ^ 2 / r := by ring
      _ ≤ 2 * (c + 1) ^ 2 / (δ ^ 2 * r) := by
          have : δ ^ 2 * r ≤ 1 * r := mul_le_mul_of_nonneg_right hδ2 hr0.le
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have t3 : 4 * X ^ 2 * (B - 1) / (r ^ 2 * δ ^ 2) ≤ 48 * (c + 1) ^ 2 / (δ ^ 2 * r) := by
    have hX2 : X ^ 2 ≤ (c + 1) ^ 2 := pow_le_pow_left₀ hX0 hX 2
    have h5 : X ^ 2 * (B - 1) ≤ (c + 1) ^ 2 * (12 * r) :=
      mul_le_mul hX2 (by linarith) (by linarith) (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h6 : 4 * X ^ 2 * (B - 1) * (δ ^ 2 * r) ≤ 4 * ((c + 1) ^ 2 * (12 * r)) * (δ ^ 2 * r) := by
      have := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 4)
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ δ ^ 2 * r)
      linarith
    have h7 : 4 * ((c + 1) ^ 2 * (12 * r)) * (δ ^ 2 * r) = 48 * (c + 1) ^ 2 * (r ^ 2 * δ ^ 2) := by
      ring
    linarith
  have : (2 * Real.exp (2 * (c + 1)) + 50 * (c + 1) ^ 2) / (δ ^ 2 * r) =
      2 * Real.exp (2 * (c + 1)) / (δ ^ 2 * r) + 2 * (c + 1) ^ 2 / (δ ^ 2 * r) +
        48 * (c + 1) ^ 2 / (δ ^ 2 * r) := by ring
  rw [this]
  linarith

/-- The key quantitative estimate, in split form. -/
theorem key_estimate_aux {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (a₁ : ι₁ → ℕ) (a₂ : ι₂ → ℕ)
    [∀ i, NeZero (a₁ i)] [∀ i, NeZero (a₂ i)]
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (hp₁ : ∀ i, (a₁ i).Prime) (hp₂ : ∀ i, (a₂ i).Prime) (h : ℕ) (hh : 1 ≤ h)
    (hle₁ : ∀ i, a₁ i ≤ h) (hlt₂ : ∀ i, h < a₂ i) (c δ : ℝ)
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hhq : |(h : ℝ) * ((∏ i, (1 - 1 / (a₁ i : ℝ))) * ∏ i, (1 - 1 / (a₂ i : ℝ))) - c| ≤ δ / 2) :
    |(∑ x₁ : (∀ i, ZMod (a₁ i)), (cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ)) /
        ((∏ i, (a₁ i : ℝ)) * ∏ i, (a₂ i : ℝ)) - Real.exp (-c)| ≤
      δ + (2 * Real.exp (2 * (c + 1)) + 50 * (c + 1) ^ 2) / (δ ^ 2 * Real.sqrt h) := by
  set M := ∏ i, (a₁ i : ℝ) with hM
  set Lp := ∏ i, (a₂ i : ℝ) with hLp
  set ρ := ∏ i, (1 - 1 / (a₁ i : ℝ)) with hρ
  set lam := ∏ i, (1 - 1 / (a₂ i : ℝ)) with hlam
  set q₁ := ∏ i, ((a₁ i : ℝ) / ((a₁ i : ℝ) - 1)) with hq₁
  set B := ∏ i, (1 + ((a₁ i : ℝ) + 1) / ((a₁ i : ℝ) - 1) ^ 2) with hB
  set r := Real.sqrt h with hr
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.2 hh'
  have hrh : (h : ℝ) = r ^ 2 := by rw [hr, Real.sq_sqrt (by linarith)]
  have hMpos : 0 < M := prod_pos fun i _ => by exact_mod_cast (hp₁ i).pos
  have hLppos : 0 < Lp := prod_pos fun i _ => by exact_mod_cast (hp₂ i).pos
  have hρq₁ : ρ = 1 / q₁ := prod_one_sub_inv_eq a₁ fun i => (hp₁ i).two_le
  have hq₁pos : 0 < q₁ := prod_pos fun i _ => by
    have : (2 : ℝ) ≤ a₁ i := by exact_mod_cast (hp₁ i).two_le
    exact div_pos (by linarith) (by linarith)
  have hq₁r : q₁ ≤ 2 * r := by
    have hsq := prod_div_sub_one_sq_le a₁ ha₁ hp₁ h hh hle₁
    have : q₁ ^ 2 ≤ (2 * r) ^ 2 := by rw [mul_pow, ← hrh]; linarith
    exact (pow_le_pow_iff_left₀ hq₁pos.le (by positivity) (by norm_num)).1 this
  have hBr : B ≤ 12 * r := by
    have := prod_B_le a₁ ha₁ fun i => (hp₁ i).two_le
    linarith
  have hlam0 : 0 ≤ lam := prod_nonneg fun i _ => by
    have : (2 : ℝ) ≤ a₂ i := by exact_mod_cast (hp₂ i).two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hlam1 : lam ≤ 1 := prod_le_one (fun i _ => by
      have : (2 : ℝ) ≤ a₂ i := by exact_mod_cast (hp₂ i).two_le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith)
    (fun i _ => by
      have : (0 : ℝ) < a₂ i := by exact_mod_cast (hp₂ i).pos
      have : 0 ≤ 1 / (a₂ i : ℝ) := by positivity
      linarith)
  have hμ : |(h * ρ) * lam - c| ≤ δ / 2 := by rw [mul_assoc]; exact hhq
  have hhl : (h * ρ) * lam ≤ c + 1 := by
    have := (abs_le.1 hμ).2; linarith
  have hρpos : 0 < ρ := by rw [hρq₁]; positivity
  have hX0 : 0 ≤ (h * ρ) * lam := by positivity
  have hr0 : 0 < r := by linarith
  have hlam_le : lam ≤ 2 * (c + 1) / r := by
    have e : lam = ((h * ρ) * lam) * q₁ / h := by
      rw [hρq₁]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) hr0]
    have h1 : ((h : ℝ) * ρ * lam) * q₁ ≤ (c + 1) * (2 * r) :=
      mul_le_mul hhl hq₁r hq₁pos.le (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 hr0.le
    have h3 : (c + 1) * (2 * r) * r = 2 * (c + 1) * h := by rw [hrh]; ring
    linarith
  have hcardV : ∀ A : Finset ℕ, (cntV a₂ A : ℝ) ≤ Lp := by
    intro A
    have : cntV a₂ A ≤ Fintype.card (∀ i, ZMod (a₂ i)) := card_le_univ _
    calc (cntV a₂ A : ℝ) ≤ (Fintype.card (∀ i, ZMod (a₂ i)) : ℝ) := by exact_mod_cast this
      _ = Lp := card_pi_zmod a₂
  have hpt : ∀ x₁ : (∀ i, ZMod (a₁ i)),
      |(cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp - Real.exp (-c)| ≤
        2 * Real.exp (2 * (c + 1)) / h + (c + 1) * lam + δ +
          4 * lam ^ 2 * ((sCount a₁ h x₁ : ℝ) - h * ρ) ^ 2 / δ ^ 2 := by
    intro x₁
    have hsA : #((range h).filter (Good a₁ x₁)) = sCount a₁ h x₁ := rfl
    have hAlt : ∀ j ∈ (range h).filter (Good a₁ x₁), ∀ i, j < a₂ i := fun j hj i =>
      lt_trans (mem_range.1 (mem_filter.1 hj).1) (hlt₂ i)
    have hEeq : (cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp =
        ∑ t ∈ range (sCount a₁ h x₁ + 1),
          (-1 : ℝ) ^ t * ((sCount a₁ h x₁).choose t : ℝ) * ∏ i, (1 - (t : ℝ) / a₂ i) := by
      rw [cntV_eq_sum a₂ _ hAlt, sum_div, hsA]
      refine sum_congr rfl fun t _ => ?_
      rw [mul_div_assoc, hLp, ← prod_div_distrib]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      have : (a₂ i : ℝ) ≠ 0 := by exact_mod_cast (hp₂ i).ne_zero
      field_simp
    have hL := Lpart_bound a₂ ha₂ h hh hlt₂ (sCount a₁ h x₁) (sCount_le a₁ h x₁)
    rw [← hEeq] at hL
    have hE0 : 0 ≤ (cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp := by positivity
    have hE1 : (cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp ≤ 1 := by
      rw [div_le_one hLppos]; exact hcardV _
    exact pointwise_bound _ lam c δ (h * ρ) (sCount a₁ h x₁) h hh hlam0 hlam1 hc
      hδ0 hδ1 hμ hE0 hE1 hL
  have hvar := sum_sCount_sub_sq_le a₁ ha₁ hp₁ h
  have hcard₁ : ((univ : Finset (∀ i, ZMod (a₁ i))).card : ℝ) = M := by
    rw [card_univ]; exact card_pi_zmod a₁
  have hdiff : (∑ x₁ : (∀ i, ZMod (a₁ i)), (cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ)) /
        (M * Lp) - Real.exp (-c) =
      (1 / M) * ∑ x₁ : (∀ i, ZMod (a₁ i)),
        ((cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp - Real.exp (-c)) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard₁, ← sum_div]
    field_simp
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / M)]
  set C0 := 2 * Real.exp (2 * (c + 1)) / h + (c + 1) * lam + δ with hC0
  have hsum : |∑ x₁ : (∀ i, ZMod (a₁ i)),
      ((cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp - Real.exp (-c))| ≤
      M * C0 + 4 * lam ^ 2 / δ ^ 2 * (M * ρ ^ 2 * h * (B - 1)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun x₁ _ => hpt x₁).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, hcard₁]
    have : ∑ x₁ : (∀ i, ZMod (a₁ i)),
        4 * lam ^ 2 * ((sCount a₁ h x₁ : ℝ) - h * ρ) ^ 2 / δ ^ 2 =
        4 * lam ^ 2 / δ ^ 2 * ∑ x₁ : (∀ i, ZMod (a₁ i)),
          ((sCount a₁ h x₁ : ℝ) - h * ρ) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun x₁ _ => by ring
    rw [this]
    have h4 : 0 ≤ 4 * lam ^ 2 / δ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hvar h4
    linarith
  have hstep : 1 / M * |∑ x₁ : (∀ i, ZMod (a₁ i)),
      ((cntV a₂ ((range h).filter (Good a₁ x₁)) : ℝ) / Lp - Real.exp (-c))| ≤
      C0 + 4 * ((h * ρ) * lam) ^ 2 * (B - 1) / (h * δ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / M)
    refine this.trans (le_of_eq ?_)
    field_simp
  refine hstep.trans ?_
  have hB0 : 1 ≤ B := by
    have := prod_le_prod (s := univ) (f := fun _ => (1 : ℝ))
      (g := fun i => 1 + ((a₁ i : ℝ) + 1) / ((a₁ i : ℝ) - 1) ^ 2) (fun _ _ => zero_le_one)
      (fun i _ => by
        have : (2 : ℝ) ≤ a₁ i := by exact_mod_cast (hp₁ i).two_le
        have : 0 ≤ ((a₁ i : ℝ) + 1) / ((a₁ i : ℝ) - 1) ^ 2 := by positivity
        linarith)
    simpa [hB] using this
  exact final_numeric c δ r h lam _ B hc hδ0 hδ1 hr1 hrh hlam_le hX0 hhl hB0 hBr

end Erdos235

namespace Erdos235

/-- The key quantitative estimate for a finite family of distinct primes. -/
theorem key_estimate {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, NeZero (a i)]
    (ha : Function.Injective a) (hp : ∀ i, (a i).Prime) (h : ℕ) (hh : 1 ≤ h) (c δ : ℝ)
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hhq : |(h : ℝ) * ∏ i, (1 - 1 / (a i : ℝ)) - c| ≤ δ / 2) :
    |(cntW a h : ℝ) / ∏ i, (a i : ℝ) - Real.exp (-c)| ≤
      δ + (2 * Real.exp (2 * (c + 1)) + 50 * (c + 1) ^ 2) / (δ ^ 2 * Real.sqrt h) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ι → Prop, Q = fun i => a i ≤ h := ⟨_, rfl⟩
  have hQi : ∀ i, Q i ↔ a i ≤ h := fun i => by rw [hQ]
  have hsplit := cntW_split a Q h
  rw [hsplit, ← Fintype.prod_subtype_mul_prod_subtype Q (fun i => (a i : ℝ))]
  push_cast
  rw [← Fintype.prod_subtype_mul_prod_subtype Q (fun i => 1 - 1 / (a i : ℝ))] at hhq
  have key := key_estimate_aux (fun i : {i // Q i} => a i) (fun i : {i // ¬ Q i} => a i)
    (fun i j hij => Subtype.ext (ha hij)) (fun i j hij => Subtype.ext (ha hij))
    (fun i => hp i) (fun i => hp i) h hh (fun i => (hQi i).1 i.2)
    (fun i => lt_of_not_ge fun hle => i.2 ((hQi i).2 hle)) c δ hc hδ0 hδ1 hhq
  convert key using 6

end Erdos235

end Part5


section Part6

open Finset Filter Topology

open scoped Classical

namespace Erdos235

lemma one_add_sum_le_prod_one_add {α : Type*} (s : Finset α) (x : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) : 1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi))
    have hx := h0 j (mem_insert_self j s)
    have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

lemma sum_range_indicator_primes (n : ℕ) :
    ∑ m ∈ range n, ({p | p.Prime} : Set ℕ).indicator (fun m => 1 / (m : ℝ)) m =
      ∑ i ∈ range (Nat.count Nat.Prime n), 1 / (Nat.nth Nat.Prime i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.count_succ]
    by_cases hn : n.Prime
    · rw [if_pos hn, sum_range_succ, Nat.nth_count hn, Set.indicator_of_mem (by exact hn)]
    · rw [if_neg hn, add_zero, Set.indicator_of_notMem (by exact hn), add_zero]

lemma tendsto_sum_inv_nth_prime :
    Tendsto (fun k => ∑ i ∈ range k, 1 / (Nat.nth Nat.Prime i : ℝ)) atTop atTop := by
  have h1 := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by
    by_cases hn : n ∈ ({p | p.Prime} : Set ℕ)
    · rw [Set.indicator_of_mem hn]; positivity
    · rw [Set.indicator_of_notMem hn])).1 not_summable_one_div_on_primes
  have h2 : Tendsto (fun k => Nat.nth Nat.Prime k) atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).tendsto_atTop
  have := h1.comp h2
  refine this.congr fun k => ?_
  simp only [Function.comp, sum_range_indicator_primes,
    Nat.count_nth_of_infinite Nat.infinite_setOf_prime]

/-- `ρ_k = ∏_{i<k} (1 - 1/p_i) = φ(N_k)/N_k`. -/
noncomputable def rhoSeq (k : ℕ) : ℝ := ∏ i ∈ range k, (1 - 1 / (Nat.nth Nat.Prime i : ℝ))

lemma rhoSeq_pos (k : ℕ) : 0 < rhoSeq k := prod_pos fun i _ => by
  have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma tendsto_rhoSeq : Tendsto rhoSeq atTop (𝓝 0) := by
  have hq : ∀ k, rhoSeq k * ∏ i ∈ range k, (1 + 1 / ((Nat.nth Nat.Prime i : ℝ) - 1)) = 1 := by
    intro k
    rw [rhoSeq, ← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    have h1 : (Nat.nth Nat.Prime i : ℝ) ≠ 0 := by linarith
    have h3 : (Nat.nth Nat.Prime i : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hge : ∀ k, ∑ i ∈ range k, 1 / (Nat.nth Nat.Prime i : ℝ) ≤
      ∏ i ∈ range k, (1 + 1 / ((Nat.nth Nat.Prime i : ℝ) - 1)) := by
    intro k
    refine le_trans ?_ (one_add_sum_le_prod_one_add _ _ fun i _ => by
      have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
      exact div_nonneg zero_le_one (by linarith))
    have : ∑ i ∈ range k, 1 / (Nat.nth Nat.Prime i : ℝ) ≤
        ∑ i ∈ range k, 1 / ((Nat.nth Nat.Prime i : ℝ) - 1) := sum_le_sum fun i _ => by
      have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hQ : Tendsto (fun k => ∏ i ∈ range k, (1 + 1 / ((Nat.nth Nat.Prime i : ℝ) - 1)))
      atTop atTop := tendsto_atTop_mono hge tendsto_sum_inv_nth_prime
  have : rhoSeq = fun k => (∏ i ∈ range k, (1 + 1 / ((Nat.nth Nat.Prime i : ℝ) - 1)))⁻¹ := by
    funext k
    exact eq_inv_of_mul_eq_one_left (hq k)
  rw [this]
  exact hQ.inv_tendsto_atTop

end Erdos235

end Part6


section Part7

open Finset Filter Topology

open scoped Classical

namespace Erdos235

instance nth_prime_neZero (n : ℕ) : NeZero (Nat.nth Nat.Prime n) :=
  ⟨(Nat.prime_nth_prime n).ne_zero⟩

/-- The first `k` primes, indexed by `Fin k`. -/
noncomputable def pk (k : ℕ) : Fin k → ℕ := fun i => Nat.nth Nat.Prime i

instance pk_neZero (k : ℕ) (i : Fin k) : NeZero (pk k i) := nth_prime_neZero _

lemma pk_injective (k : ℕ) : Function.Injective (pk k) := fun _ _ hij =>
  Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij)

lemma pk_prime (k : ℕ) (i : Fin k) : (pk k i).Prime := Nat.prime_nth_prime _

lemma prod_pk_one_sub (k : ℕ) : ∏ i, (1 - 1 / (pk k i : ℝ)) = rhoSeq k :=
  Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (Nat.nth Nat.Prime i : ℝ)) k

lemma tendsto_of_mul_rhoSeq {c : ℝ} (hc : 0 < c) {f : ℕ → ℝ}
    (hlim : Tendsto (fun k => f k * rhoSeq k) atTop (𝓝 c)) : Tendsto f atTop atTop := by
  have h1 : Tendsto rhoSeq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_rhoSeq, Eventually.of_forall rhoSeq_pos⟩
  have h2 := hlim.pos_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp h1)
  refine h2.congr fun k => ?_
  have := (rhoSeq_pos k).ne'
  simp only [Function.comp]
  field_simp

/-- Main analytic input: if `h_k ρ_k → c > 0` then `W_k(h_k)/N_k → e^{-c}`. -/
theorem tendsto_cntW {c : ℝ} (hc : 0 < c) (hk : ℕ → ℕ)
    (hlim : Tendsto (fun k => (hk k : ℝ) * rhoSeq k) atTop (𝓝 c)) :
    Tendsto (fun k => (cntW (pk k) (hk k) : ℝ) / ∏ i, (pk k i : ℝ)) atTop
      (𝓝 (Real.exp (-c))) := by
  have hH := tendsto_of_mul_rhoSeq hc hlim
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := min 1 (ε / 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / 2 := min_le_right _ _
  set K := 2 * Real.exp (2 * (c + 1)) + 50 * (c + 1) ^ 2
  have hT : Tendsto (fun k => K / (δ ^ 2 * Real.sqrt (hk k))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop (by positivity) (Real.tendsto_sqrt_atTop.comp hH))
  have e1 := (Metric.tendsto_atTop.1 hT) (ε / 2) (by linarith)
  have e2 := (Metric.tendsto_atTop.1 hlim) (δ / 2) (by linarith)
  have e3 := (tendsto_atTop.1 hH) 1
  rw [eventually_atTop] at e3
  obtain ⟨N1, hN1⟩ := e1
  obtain ⟨N2, hN2⟩ := e2
  obtain ⟨N3, hN3⟩ := e3
  refine ⟨max N1 (max N2 N3), fun k hk' => ?_⟩
  have k1 : N1 ≤ k := le_trans (le_max_left _ _) hk'
  have k2 : N2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk'
  have k3 : N3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk'
  have a1 := hN1 k k1
  have a2 := hN2 k k2
  have a3 := hN3 k k3
  rw [Real.dist_eq, sub_zero] at a1
  rw [Real.dist_eq] at a2 ⊢
  have hh1 : 1 ≤ hk k := by exact_mod_cast a3
  have key := key_estimate (pk k) (pk_injective k) (pk_prime k) (hk k) hh1 c δ hc hδ0 hδ1
    (by rw [prod_pk_one_sub]; exact a2.le)
  have : K / (δ ^ 2 * Real.sqrt (hk k)) < ε / 2 := lt_of_abs_lt a1
  linarith

end Erdos235

end Part7


section Part8

open Finset Filter Topology

open scoped Classical

namespace Erdos235

/-- `N_k` as a product over `Fin k`. -/
noncomputable def NN (k : ℕ) : ℕ := ∏ i, pk k i

instance NN_neZero (k : ℕ) : NeZero (NN k) :=
  ⟨by unfold NN; exact prod_ne_zero_iff.2 fun i _ => NeZero.ne _⟩

lemma pk_coprime (k : ℕ) : Pairwise (Function.onFun Nat.Coprime (pk k)) := fun i j hij =>
  (Nat.coprime_primes (pk_prime k i) (pk_prime k j)).2 (fun h => hij (pk_injective k h))

/-- Chinese remainder theorem for `N_k`. -/
noncomputable def crt (k : ℕ) : ZMod (NN k) ≃+* ∀ i, ZMod (pk k i) :=
  ZMod.prodEquivPi (pk k) (pk_coprime k)

lemma isUnit_add_iff_good (k : ℕ) (x : ZMod (NN k)) (j : ℕ) :
    IsUnit (x + j) ↔ Good (pk k) (crt k x) j := by
  haveI : ∀ i, Fact (pk k i).Prime := fun i => ⟨pk_prime k i⟩
  rw [← MulEquiv.isUnit_map (crt k).toMulEquiv, Pi.isUnit_iff]
  simp only [Good, isUnit_iff_ne_zero]
  simp

/-- `W(h)`: number of `x mod N_k` such that none of `x, …, x+h-1` is a unit. -/
noncomputable def WZ (k h : ℕ) : ℕ := #{x : ZMod (NN k) | ∀ j ∈ range h, ¬ IsUnit (x + j)}

/-- `E(h)`: number of units `x mod N_k` such that none of `x+1, …, x+h` is a unit. -/
noncomputable def EZ (k h : ℕ) : ℕ :=
  #{x : ZMod (NN k) | IsUnit x ∧ ∀ j ∈ range h, ¬ IsUnit (x + ((j + 1 : ℕ) : ZMod (NN k)))}

lemma WZ_eq_cntW (k h : ℕ) : WZ k h = cntW (pk k) h :=
  card_equiv (crt k).toEquiv fun x => by
    simp only [mem_filter, mem_univ, true_and, isUnit_add_iff_good]; rfl

lemma card_units_NN (k : ℕ) : #{x : ZMod (NN k) | IsUnit x} = ∏ i, (pk k i - 1) := by
  have h := card_forall_good (pk k) {0}
  simp only [image_singleton, card_singleton] at h
  rw [← h]
  refine card_equiv (crt k).toEquiv fun x => ?_
  have := isUnit_add_iff_good k x 0
  simp only [Nat.cast_zero, add_zero] at this
  simp only [mem_filter, mem_univ, true_and, mem_singleton, forall_eq, this]; rfl

lemma WZ_succ (k h : ℕ) : WZ k h = WZ k (h + 1) + EZ k h := by
  have h1 : WZ k h = #{y : ZMod (NN k) | ∀ j ∈ range h,
      ¬ IsUnit (y + ((j + 1 : ℕ) : ZMod (NN k)))} := by
    refine card_equiv (Equiv.addRight (-1)) fun x => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, Nat.cast_add, Nat.cast_one]
    refine forall₂_congr fun j _ => ?_
    rw [show x + -1 + ((j : ZMod (NN k)) + 1) = x + j by ring]
  rw [h1, ← card_filter_add_card_filter_not (p := fun y : ZMod (NN k) => IsUnit y), add_comm]
  congr 2
  · ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hy, hu⟩ j hj
      rcases j with _ | j
      · simpa using hu
      · exact hy j (by simp at hj ⊢; omega)
    · intro hy
      refine ⟨fun j hj => hy (j + 1) (by simp at hj ⊢; omega), ?_⟩
      simpa using hy 0 (by simp)
  · ext y
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm

lemma EZ_succ_le (k h : ℕ) : EZ k (h + 1) ≤ EZ k h := by
  refine card_le_card fun x => ?_
  simp only [mem_filter, mem_univ, true_and]
  exact fun ⟨hx, hy⟩ => ⟨hx, fun j hj => hy j (by simp at hj ⊢; omega)⟩

end Erdos235

end Part8


section Part9

open Finset Filter Topology

open scoped Classical

namespace Erdos235

/-- `φ(N_k)` as a real number, counted as the number of units of `ZMod N_k`. -/
noncomputable def phiK (k : ℕ) : ℝ := #{x : ZMod (NN k) | IsUnit x}

lemma NN_cast (k : ℕ) : (NN k : ℝ) = ∏ i, (pk k i : ℝ) := by
  unfold NN; push_cast; rfl

lemma NN_pos (k : ℕ) : (0 : ℝ) < NN k := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (NN k))

lemma phiK_eq (k : ℕ) : phiK k = NN k * rhoSeq k := by
  rw [phiK, card_units_NN, NN_cast, ← prod_pk_one_sub, ← prod_mul_distrib, Nat.cast_prod]
  refine prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ pk k i := (pk_prime k i).one_le
  have h2 : (pk k i : ℝ) ≠ 0 := by exact_mod_cast (pk_prime k i).ne_zero
  rw [Nat.cast_sub h1]
  field_simp
  push_cast
  ring

lemma phiK_pos (k : ℕ) : 0 < phiK k := by
  rw [phiK_eq]; exact mul_pos (NN_pos k) (rhoSeq_pos k)

/-- Abstract summation-by-parts sandwich. -/
lemma sandwich (W E : ℕ → ℕ) (hrec : ∀ h, W h = W (h + 1) + E h)
    (hanti : ∀ h, E (h + 1) ≤ E h) (h H : ℕ) :
    W (h + H) + H * E (h + H) ≤ W h ∧ W h ≤ W (h + H) + H * E h := by
  have hA : Antitone E := antitone_nat_of_succ_le hanti
  induction H with
  | zero => simp
  | succ H ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have r := hrec (h + H)
    have a1 : E (h + (H + 1)) ≤ E (h + H) := hA (by omega)
    have a2 : E (h + H) ≤ E h := hA (by omega)
    have m1 : H * E (h + (H + 1)) ≤ H * E (h + H) := Nat.mul_le_mul_left _ a1
    rw [show h + (H + 1) = h + H + 1 by ring] at a1 m1 ⊢
    constructor
    · nlinarith
    · nlinarith

lemma real_sandwich (W0 W1 W2 E N ρ H : ℝ) (hN : 0 < N) (hρ : 0 < ρ) (hH : 0 < H)
    (h1 : W0 ≤ W1 + H * E) (h2 : W0 + H * E ≤ W2) :
    (W0 / N - W1 / N) / (H * ρ) ≤ E / (N * ρ) ∧ E / (N * ρ) ≤ (W2 / N - W0 / N) / (H * ρ) := by
  constructor
  · rw [← sub_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (W0 - W1) * (H * ρ) ≤ H * E * (H * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  · rw [← sub_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : H * E * (H * ρ) ≤ (W2 - W0) * (H * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith

lemma lo_bound (c ε : ℝ) (hc : 0 ≤ c) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-c) - ε ≤ (Real.exp (-c) - Real.exp (-(c + ε))) / ε := by
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := -ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε1)
  have h2 : Real.exp (-ε) ≤ 1 - ε + ε ^ 2 := by
    have := (abs_le.1 h1).2; nlinarith
  have he : Real.exp (-(c + ε)) = Real.exp (-c) * Real.exp (-ε) := by
    rw [← Real.exp_add]; ring_nf
  have hc1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hc0 : 0 < Real.exp (-c) := Real.exp_pos _
  rw [le_div_iff₀ hε0, he]
  have : Real.exp (-c) * Real.exp (-ε) ≤ Real.exp (-c) * (1 - ε + ε ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hc0.le
  nlinarith

lemma hi_bound (c ε : ℝ) (hc : 0 ≤ c) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.exp (-(c - ε)) - Real.exp (-c)) / ε ≤ Real.exp (-c) + ε := by
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := ε) (by rw [abs_of_pos hε0]; exact hε1)
  have h2 : Real.exp ε ≤ 1 + ε + ε ^ 2 := by
    have := (abs_le.1 h1).2; nlinarith
  have he : Real.exp (-(c - ε)) = Real.exp (-c) * Real.exp ε := by
    rw [← Real.exp_add]; ring_nf
  have hc1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hc0 : 0 < Real.exp (-c) := Real.exp_pos _
  rw [div_le_iff₀ hε0, he]
  have : Real.exp (-c) * Real.exp ε ≤ Real.exp (-c) * (1 + ε + ε ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hc0.le
  nlinarith

lemma tendsto_floor_div_rho {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun k => (⌊a / rhoSeq k⌋₊ : ℝ) * rhoSeq k) atTop (𝓝 a) := by
  have hl : Tendsto (fun k => a - rhoSeq k) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub tendsto_rhoSeq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun k => ?_) (fun k => ?_)
  · have hr := rhoSeq_pos k
    have := Nat.lt_floor_add_one (a / rhoSeq k)
    have h2 : a / rhoSeq k * rhoSeq k = a := div_mul_cancel₀ a hr.ne'
    nlinarith
  · have hr := rhoSeq_pos k
    have := Nat.floor_le (div_nonneg ha hr.le)
    have h2 : a / rhoSeq k * rhoSeq k = a := div_mul_cancel₀ a hr.ne'
    nlinarith

lemma cntW_div_eq (k h : ℕ) :
    (cntW (pk k) h : ℝ) / ∏ i, (pk k i : ℝ) = (WZ k h : ℝ) / NN k := by
  rw [WZ_eq_cntW, NN_cast]

lemma EZ_zero (k : ℕ) : EZ k 0 = #{x : ZMod (NN k) | IsUnit x} := by
  unfold EZ
  refine congrArg card (filter_congr fun x _ => ?_)
  simp

/-- `E_k(⌊c N_k/φ(N_k)⌋)/φ(N_k) → e^{-c}`. -/
theorem tendsto_EZ {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun k => (EZ k ⌊c / rhoSeq k⌋₊ : ℝ) / phiK k) atTop (𝓝 (Real.exp (-c))) := by
  rcases hc.eq_or_lt with rfl | hc
  · have : ∀ k, (EZ k ⌊0 / rhoSeq k⌋₊ : ℝ) / phiK k = 1 := fun k => by
      rw [zero_div, Nat.floor_zero, div_eq_one_iff_eq (phiK_pos k).ne', phiK, EZ_zero]
    simp only [this, neg_zero, Real.exp_zero]
    exact tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := min (c / 2) (min (η / 4) 1) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) one_pos)
  have hεc : ε ≤ c / 2 := min_le_left _ _
  have hεη : ε ≤ η / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  set h0 : ℕ → ℕ := fun k => ⌊c / rhoSeq k⌋₊ with hh0
  set H : ℕ → ℕ := fun k => ⌊ε / rhoSeq k⌋₊ with hH
  have hHle : ∀ k, H k ≤ h0 k := fun k =>
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) (rhoSeq_pos k).le)
  have t0 : Tendsto (fun k => (h0 k : ℝ) * rhoSeq k) atTop (𝓝 c) := tendsto_floor_div_rho hc.le
  have tH : Tendsto (fun k => (H k : ℝ) * rhoSeq k) atTop (𝓝 ε) := tendsto_floor_div_rho hε0.le
  have t1 : Tendsto (fun k => ((h0 k + H k : ℕ) : ℝ) * rhoSeq k) atTop (𝓝 (c + ε)) :=
    (t0.add tH).congr fun k => by push_cast; ring
  have t2 : Tendsto (fun k => ((h0 k - H k : ℕ) : ℝ) * rhoSeq k) atTop (𝓝 (c - ε)) :=
    (t0.sub tH).congr fun k => by rw [Nat.cast_sub (hHle k)]; ring
  have w0 := tendsto_cntW hc h0 t0
  have w1 := tendsto_cntW (by linarith) (fun k => h0 k + H k) t1
  have w2 := tendsto_cntW (by linarith) (fun k => h0 k - H k) t2
  simp only [cntW_div_eq] at w0 w1 w2
  have tlo : Tendsto (fun k => ((WZ k (h0 k) : ℝ) / NN k - (WZ k (h0 k + H k) : ℝ) / NN k) /
      ((H k : ℝ) * rhoSeq k)) atTop
      (𝓝 ((Real.exp (-c) - Real.exp (-(c + ε))) / ε)) := (w0.sub w1).div tH hε0.ne'
  have thi : Tendsto (fun k => ((WZ k (h0 k - H k) : ℝ) / NN k - (WZ k (h0 k) : ℝ) / NN k) /
      ((H k : ℝ) * rhoSeq k)) atTop
      (𝓝 ((Real.exp (-(c - ε)) - Real.exp (-c)) / ε)) := (w2.sub w0).div tH hε0.ne'
  have lb := lo_bound c ε hc.le hε0 hε1
  have ub := hi_bound c ε hc.le hε0 hε1
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 tlo) (η / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 thi) (η / 2) (by linarith)
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.1 tH) (ε / 2) (by linarith)
  refine ⟨max N1 (max N2 N3), fun k hk' => ?_⟩
  have a1 := hN1 k (le_trans (le_max_left _ _) hk')
  have a2 := hN2 k (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk')
  have a3 := hN3 k (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk')
  rw [Real.dist_eq] at a1 a2 a3 ⊢
  have hρ := rhoSeq_pos k
  have hHpos : (0 : ℝ) < H k := by
    by_contra hneg
    have : (H k : ℝ) = 0 := le_antisymm (not_lt.1 hneg) (Nat.cast_nonneg _)
    rw [this, zero_mul, zero_sub, abs_neg, abs_of_pos hε0] at a3
    linarith
  have sw1 := (sandwich (WZ k) (EZ k) (WZ_succ k) (EZ_succ_le k) (h0 k) (H k)).2
  have sw2 := (sandwich (WZ k) (EZ k) (WZ_succ k) (EZ_succ_le k) (h0 k - H k) (H k)).1
  rw [Nat.sub_add_cancel (hHle k)] at sw2
  have rs := real_sandwich (WZ k (h0 k)) (WZ k (h0 k + H k)) (WZ k (h0 k - H k))
    (EZ k (h0 k)) (NN k) (rhoSeq k) (H k) (NN_pos k) hρ hHpos
    (by exact_mod_cast sw1) (by exact_mod_cast sw2)
  rw [phiK_eq]
  obtain ⟨r1, r2⟩ := rs
  have b1 := (abs_lt.1 a1).1
  have b2 := (abs_lt.1 a2).2
  rw [abs_lt]
  constructor <;> linarith

end Erdos235

end Part9


section Part10

open Finset Filter Topology

open scoped Classical

namespace Erdos235

lemma coprime_self_succ (m : ℕ) : m.Coprime (m + 1) := by
  rw [add_comm, Nat.coprime_add_self_right]; exact Nat.coprime_one_right _

/-! ### Sorted lists -/

lemma sort_next_le (l : List ℕ) (hs : l.SortedLT) (i : ℕ) (hi : i < l.length) (hi1 : 1 ≤ i)
    (m : ℕ) (hm : m ∈ l) (hlt : l[i - 1] < m) : l[i] ≤ m := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hm
  have : i - 1 < j := hs.getElem_lt_getElem_iff.1 hlt
  rcases (show i = j ∨ i < j by omega) with rfl | h
  · exact le_rfl
  · exact (hs.getElem_lt_getElem_iff.2 h).le

lemma card_gap_eq_aux (R : Finset ℕ) (l : List ℕ) (hs : l.SortedLT) (hmem : ∀ m, m ∈ R ↔ m ∈ l)
    (h : ℕ) :
    #{i ∈ Ico 1 l.length | l[i - 1]! + h < l[i]!} =
      #{m ∈ R | (∃ m' ∈ R, m < m') ∧ ∀ m' ∈ R, m < m' → m + h < m'} := by
  refine Finset.card_bij (fun i _ => l[i - 1]!) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_Ico] at hi ⊢
    obtain ⟨⟨hi1, hi2⟩, hg⟩ := hi
    rw [getElem!_pos l (i - 1) (by omega), getElem!_pos l i hi2] at hg
    rw [getElem!_pos l (i - 1) (by omega)]
    refine ⟨(hmem _).2 (List.getElem_mem _), ⟨l[i], (hmem _).2 (List.getElem_mem _),
      by omega⟩, fun m' hm' hlt => ?_⟩
    have := sort_next_le l hs i hi2 hi1 m' ((hmem _).1 hm') hlt
    omega
  · intro i hi j hj hij
    simp only [mem_filter, mem_Ico] at hi hj
    simp only at hij
    rw [getElem!_pos l (i - 1) (by omega), getElem!_pos l (j - 1) (by omega)] at hij
    have := (hs.nodup.getElem_inj_iff).1 hij
    omega
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨hmR, ⟨m', hm'R, hlt⟩, hgap⟩ := hm
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 ((hmem _).1 hmR)
    obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.1 ((hmem _).1 hm'R)
    have htu : t < u := hs.getElem_lt_getElem_iff.1 hlt
    refine ⟨t + 1, ?_, ?_⟩
    · simp only [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [getElem!_pos l (t + 1 - 1) (by omega), getElem!_pos l (t + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      exact hgap _ ((hmem _).2 (List.getElem_mem _))
        (hs.getElem_lt_getElem_iff.2 (Nat.lt_succ_self t))
    · show l[t + 1 - 1]! = l[t]
      simp only [Nat.add_sub_cancel]
      exact getElem!_pos l t ht

lemma card_gap_eq (R : Finset ℕ) (h : ℕ) :
    #{i ∈ Ico 1 (R.sort (· ≤ ·)).length | (R.sort (· ≤ ·))[i - 1]! + h < (R.sort (· ≤ ·))[i]!} =
      #{m ∈ R | (∃ m' ∈ R, m < m') ∧ ∀ m' ∈ R, m < m' → m + h < m'} :=
  card_gap_eq_aux R _ (Finset.sortedLT_sort R) (fun _ => (Finset.mem_sort _).symm) h

/-! ### From `ZMod N` to integers in `[0, N)` -/

lemma isUnit_add_natCast_iff (N : ℕ) [NeZero N] (x : ZMod N) (n : ℕ) :
    IsUnit (x + n) ↔ ((x.val + n) % N).Coprime N := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_add, ← ZMod.natCast_mod, ZMod.isUnit_iff_coprime]

lemma isUnit_iff_val_coprime (N : ℕ) [NeZero N] (x : ZMod N) :
    IsUnit x ↔ x.val.Coprime N := by
  have := isUnit_add_natCast_iff N x 0
  rwa [Nat.cast_zero, add_zero, add_zero, Nat.mod_eq_of_lt (ZMod.val_lt x)] at this

lemma card_EZset_eq (N : ℕ) [NeZero N] (h : ℕ) :
    #{x : ZMod N | IsUnit x ∧ ∀ j ∈ range h, ¬ IsUnit (x + ((j + 1 : ℕ) : ZMod N))} =
      #{m ∈ (range N).filter (fun m => m.Coprime N) |
        ∀ j ∈ range h, ¬ ((m + (j + 1)) % N).Coprime N} := by
  refine Finset.card_nbij' (fun x : ZMod N => x.val) (fun m => (m : ZMod N)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_filter, mem_range] at hx ⊢
    obtain ⟨hu, hj⟩ := hx
    refine ⟨⟨ZMod.val_lt x, (isUnit_iff_val_coprime N x).1 hu⟩, fun j hjr => ?_⟩
    rw [← isUnit_add_natCast_iff]
    exact hj j hjr
  · intro m hm
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_filter, mem_range] at hm ⊢
    obtain ⟨⟨hmN, hc⟩, hj⟩ := hm
    have hv : (m : ZMod N).val = m := ZMod.val_cast_of_lt hmN
    refine ⟨(isUnit_iff_val_coprime N _).2 (by rwa [hv]), fun j hjr => ?_⟩
    rw [isUnit_add_natCast_iff, hv]
    exact hj j hjr
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro m hm
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_range] at hm
    exact ZMod.val_cast_of_lt hm.1.1

lemma S'_subset_S (N h : ℕ) :
    {m ∈ (range N).filter (fun m => m.Coprime N) |
        (∃ m' ∈ (range N).filter (fun m => m.Coprime N), m < m') ∧
          ∀ m' ∈ (range N).filter (fun m => m.Coprime N), m < m' → m + h < m'} ⊆
      {m ∈ (range N).filter (fun m => m.Coprime N) |
        ∀ j ∈ range h, ¬ ((m + (j + 1)) % N).Coprime N} := by
  intro m hm
  simp only [mem_filter, mem_range] at hm ⊢
  obtain ⟨hmR, ⟨m', ⟨hm'N, _⟩, hlt⟩, hgap⟩ := hm
  refine ⟨hmR, fun j hj hc => ?_⟩
  have hlt' : m + h < m' := hgap m' ⟨hm'N, by assumption⟩ hlt
  have hsmall : m + (j + 1) < N := by omega
  rw [Nat.mod_eq_of_lt hsmall] at hc
  have := hgap (m + (j + 1)) ⟨hsmall, hc⟩ (by omega)
  omega

lemma S_subset_insert (N h : ℕ) (hN : 0 < N) :
    {m ∈ (range N).filter (fun m => m.Coprime N) |
        ∀ j ∈ range h, ¬ ((m + (j + 1)) % N).Coprime N} ⊆
      insert (N - 1) {m ∈ (range N).filter (fun m => m.Coprime N) |
        (∃ m' ∈ (range N).filter (fun m => m.Coprime N), m < m') ∧
          ∀ m' ∈ (range N).filter (fun m => m.Coprime N), m < m' → m + h < m'} := by
  intro m hm
  simp only [mem_filter, mem_range] at hm
  obtain ⟨⟨hmN, hmc⟩, hj⟩ := hm
  rw [mem_insert]
  by_cases hm1 : m = N - 1
  · exact Or.inl hm1
  right
  simp only [mem_filter, mem_range]
  have hc1 : (N - 1).Coprime N := by
    have := coprime_self_succ (N - 1)
    rwa [Nat.sub_add_cancel hN] at this
  refine ⟨⟨hmN, hmc⟩, ⟨N - 1, ⟨by omega, hc1⟩, by omega⟩, fun m' ⟨hm'N, hm'c⟩ hlt => ?_⟩
  by_contra hle
  have := hj (m' - m - 1) (by omega)
  rw [show m + (m' - m - 1 + 1) = m' by omega, Nat.mod_eq_of_lt hm'N] at this
  exact this hm'c

end Erdos235

end Part10


section Part11

open Finset Filter Topology

open scoped Classical

namespace Erdos235

/-- `N_k = p_1 p_2 ⋯ p_k`, the product of the first `k` primes. -/
noncomputable def primorialN (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i

/-- The integers `0 ≤ a < N` coprime to `N`, listed in increasing order. -/
def reducedResidues (N : ℕ) : List ℕ :=
  ((range N).filter (fun m => m.Coprime N)).sort (· ≤ ·)

/-- The proportion of indices `2 ≤ i ≤ φ(N_k)` (`1 ≤ i < φ(N_k)` with `0`-based indexing)
with `a_i - a_{i-1} ≤ c N_k / φ(N_k)`. -/
noncomputable def gapProportion (k : ℕ) (c : ℝ) : ℝ :=
  (#{i ∈ Ico 1 (reducedResidues (primorialN k)).length |
      (((reducedResidues (primorialN k))[i]! : ℕ) : ℝ) -
          (((reducedResidues (primorialN k))[i - 1]! : ℕ) : ℝ) ≤
        c * primorialN k / (primorialN k).totient} : ℝ) / (primorialN k).totient

lemma primorialN_eq_NN (k : ℕ) : primorialN k = NN k :=
  (Fin.prod_univ_eq_prod_range (fun i => Nat.nth Nat.Prime i) k).symm

lemma real_sub_le_iff (a b : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (b : ℝ) - a ≤ T ↔ ¬ (a + ⌊T⌋₊ < b) := by
  rw [not_lt]
  rcases le_total a b with hab | hab
  · rw [← Nat.cast_sub hab, ← Nat.le_floor_iff hT]
    omega
  · have : (b : ℝ) - a ≤ 0 := by
      have : (b : ℝ) ≤ a := by exact_mod_cast hab
      linarith
    exact ⟨fun _ => by omega, fun _ => by linarith⟩

lemma count_add_B (l : List ℕ) {T : ℝ} (hT : 0 ≤ T) :
    #{i ∈ Ico 1 l.length | ((l[i]! : ℕ) : ℝ) - ((l[i - 1]! : ℕ) : ℝ) ≤ T} +
      #{i ∈ Ico 1 l.length | l[i - 1]! + ⌊T⌋₊ < l[i]!} = l.length - 1 := by
  rw [← Nat.card_Ico 1 l.length,
    ← card_filter_add_card_filter_not (s := Ico 1 l.length)
      (p := fun i => l[i - 1]! + ⌊T⌋₊ < l[i]!), add_comm]
  congr 2
  exact filter_congr fun i _ => real_sub_le_iff _ _ hT

/-- Number of gaps exceeding `h` in the reduced residue system mod `N_k`. -/
noncomputable def Bk (k h : ℕ) : ℕ :=
  #{i ∈ Ico 1 (reducedResidues (NN k)).length |
    (reducedResidues (NN k))[i - 1]! + h < (reducedResidues (NN k))[i]!}

lemma EZ_eq_S (k h : ℕ) : EZ k h = #{m ∈ (range (NN k)).filter (fun m => m.Coprime (NN k)) |
    ∀ j ∈ range h, ¬ ((m + (j + 1)) % NN k).Coprime (NN k)} :=
  card_EZset_eq (NN k) h

lemma Bk_le_EZ (k h : ℕ) : Bk k h ≤ EZ k h := by
  rw [Bk, reducedResidues, card_gap_eq, EZ_eq_S]
  exact card_le_card (S'_subset_S _ _)

lemma EZ_le_Bk (k h : ℕ) : EZ k h ≤ Bk k h + 1 := by
  rw [Bk, reducedResidues, card_gap_eq, EZ_eq_S]
  exact (card_le_card (S_subset_insert _ _ (Nat.pos_of_ne_zero (NeZero.ne _)))).trans
    (card_insert_le _ _)

lemma length_reducedResidues (k : ℕ) :
    ((reducedResidues (NN k)).length : ℝ) = phiK k := by
  rw [reducedResidues, Finset.length_sort, phiK, ← EZ_zero, EZ_eq_S]
  congr 2
  exact (filter_true_of_mem fun m _ => by simp).symm

lemma totient_NN (k : ℕ) : ((NN k).totient : ℝ) = phiK k := by
  rw [← length_reducedResidues, reducedResidues, Finset.length_sort, Nat.totient_eq_card_coprime]
  congr 2
  exact filter_congr fun m _ => Nat.coprime_comm

lemma gapProportion_eq (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    gapProportion k c = 1 - 1 / phiK k - (Bk k ⌊c / rhoSeq k⌋₊ : ℝ) / phiK k := by
  have hφ := phiK_pos k
  have hT : c * (NN k : ℝ) / phiK k = c / rhoSeq k := by
    rw [phiK_eq]; have := NN_pos k; have := rhoSeq_pos k; field_simp
  have hT0 : 0 ≤ c / rhoSeq k := div_nonneg hc (rhoSeq_pos k).le
  have hcount := count_add_B (reducedResidues (NN k)) hT0
  have hlen : 1 ≤ (reducedResidues (NN k)).length := by
    have := length_reducedResidues k
    have h1 : (0 : ℝ) < (reducedResidues (NN k)).length := by rw [this]; exact hφ
    exact_mod_cast h1
  have hcount' : (#{i ∈ Ico 1 (reducedResidues (NN k)).length |
      (((reducedResidues (NN k))[i]! : ℕ) : ℝ) - (((reducedResidues (NN k))[i - 1]! : ℕ) : ℝ) ≤
        c / rhoSeq k} : ℝ)
      = phiK k - 1 - Bk k ⌊c / rhoSeq k⌋₊ := by
    rw [← length_reducedResidues, Bk]
    have := congrArg (fun n : ℕ => (n : ℝ)) hcount
    simp only [Nat.cast_add, Nat.cast_sub hlen, Nat.cast_one] at this
    linarith
  rw [gapProportion, primorialN_eq_NN, totient_NN, hT, hcount']
  field_simp

lemma nth_prime_ge (i : ℕ) : i + 2 ≤ Nat.nth Nat.Prime i := by
  induction i with
  | zero => rw [Nat.nth_prime_zero_eq_two]
  | succ i ih =>
    have : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
    omega

lemma phiK_ge (k : ℕ) : (k : ℝ) ≤ phiK k := by
  rw [phiK, card_units_NN]
  have : k ≤ ∏ i, (pk k i - 1) := by
    rcases k with _ | m
    · exact Nat.zero_le _
    · have h1 : ∀ i ∈ (univ : Finset (Fin (m + 1))), 1 ≤ pk (m + 1) i - 1 := fun i _ => by
        have := (pk_prime (m + 1) i).two_le; omega
      refine le_trans ?_ (single_le_prod' h1 (mem_univ (Fin.last m)))
      have := nth_prime_ge m
      simp only [pk, Fin.val_last]
      omega
  exact_mod_cast this

lemma tendsto_inv_phiK : Tendsto (fun k => 1 / phiK k) atTop (𝓝 0) := by
  have : Tendsto phiK atTop atTop :=
    tendsto_atTop_mono phiK_ge tendsto_natCast_atTop_atTop
  simpa only [one_div] using this.inv_tendsto_atTop

/-- **Erdős Problem 235 (Hooley).** For every `c ≥ 0`, the proportion of gaps
`a_i - a_{i-1} ≤ c N_k / φ(N_k)` among the reduced residues mod `N_k` tends to `1 - e^{-c}`. -/
theorem erdos_235 {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun k => gapProportion k c) atTop (𝓝 (1 - Real.exp (-c))) := by
  have hE := tendsto_EZ hc
  have hlow : Tendsto (fun k => (EZ k ⌊c / rhoSeq k⌋₊ : ℝ) / phiK k - 1 / phiK k) atTop
      (𝓝 (Real.exp (-c))) := by simpa using hE.sub tendsto_inv_phiK
  have hB : Tendsto (fun k => (Bk k ⌊c / rhoSeq k⌋₊ : ℝ) / phiK k) atTop
      (𝓝 (Real.exp (-c))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hE (fun k => ?_) (fun k => ?_)
    · have := phiK_pos k
      have h := EZ_le_Bk k ⌊c / rhoSeq k⌋₊
      rw [← sub_div, div_le_div_iff_of_pos_right this]
      have : (EZ k ⌊c / rhoSeq k⌋₊ : ℝ) ≤ Bk k ⌊c / rhoSeq k⌋₊ + 1 := by exact_mod_cast h
      linarith
    · have := phiK_pos k
      rw [div_le_div_iff_of_pos_right this]
      exact_mod_cast Bk_le_EZ k _
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_phiK |>.sub hB
  rw [sub_zero] at this
  exact this.congr fun k => (gapProportion_eq k hc).symm

/-- The limit exists for every `c ≥ 0` and is a continuous function of `c`. -/
theorem erdos_235_continuous :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ c : ℝ, 0 ≤ c → Tendsto (fun k => gapProportion k c) atTop (𝓝 (f c)) :=
  ⟨fun c => 1 - Real.exp (-c), by fun_prop, fun _ hc => erdos_235 hc⟩

end Erdos235

end Part11


end
