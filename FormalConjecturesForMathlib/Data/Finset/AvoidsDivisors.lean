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

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Real.Basic
public import FormalConjecturesForMathlib.Data.Finset.ReciprocalSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace Finset

/-- The integers in `{1, …, x}` not divisible by any element of `A`. -/
def avoidsDivisors (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun m => ∀ a ∈ A, ¬ a ∣ m)

@[simp]
lemma mem_avoidsDivisors {A : Finset ℕ} {x m : ℕ} :
    m ∈ avoidsDivisors A x ↔ m ∈ Icc 1 x ∧ ∀ a ∈ A, ¬ a ∣ m := by
  simp [avoidsDivisors]

lemma avoidsDivisors_empty (x : ℕ) :
    avoidsDivisors ∅ x = Icc 1 x := by
  simp [avoidsDivisors]

/-- Enlarging the divisor set can only shrink the set of unsieved integers. -/
lemma avoidsDivisors_mono {A B : Finset ℕ} (h : A ⊆ B) (x : ℕ) :
    avoidsDivisors B x ⊆ avoidsDivisors A x := by
  intro m hm
  simp only [mem_avoidsDivisors] at hm ⊢
  exact ⟨hm.1, fun a ha ↦ hm.2 a (h ha)⟩

/-- If `1 ∈ A`, then every `m` is divisible by an element of `A`, so nothing survives. -/
lemma avoidsDivisors_eq_empty_of_one_mem {A : Finset ℕ} (h : 1 ∈ A) (x : ℕ) :
    avoidsDivisors A x = ∅ := by
  refine eq_empty_of_forall_notMem fun m hm ↦ ?_
  have hA : ∀ a ∈ A, ¬a ∣ m := (mem_avoidsDivisors.mp hm).2
  exact hA 1 h (one_dvd m)

/-- The unsieved set is a subset of `{1, …, x}`, so its cardinality is at most `x`. -/
lemma card_avoidsDivisors_le (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors A x).card ≤ x := by
  have hsub : avoidsDivisors A x ⊆ Icc 1 x := filter_subset _ _
  exact (card_le_card hsub).trans (by simp [Nat.card_Icc])

/-- Sieving by a union is the intersection of the two sifted sets. -/
lemma avoidsDivisors_union (A B : Finset ℕ) (x : ℕ) :
    avoidsDivisors (A ∪ B) x = avoidsDivisors A x ∩ avoidsDivisors B x := by
  ext m
  simp only [mem_avoidsDivisors, mem_union, mem_inter, or_imp, forall_and]
  tauto

/-- With an empty sieve, every integer in `{1, …, x}` survives. -/
@[simp]
lemma card_avoidsDivisors_empty (x : ℕ) : (avoidsDivisors ∅ x).card = x := by
  simp [avoidsDivisors_empty, Nat.card_Icc]

/-- The number of multiples of `a` in `{1, …, x}` is `⌊x / a⌋`. -/
lemma card_Icc_filter_dvd (a x : ℕ) :
    #{m ∈ Icc 1 x | a ∣ m} = x / a := by
  convert Nat.Ioc_filter_dvd_card_eq_div x a using 2
  ext m
  simp [mem_Icc, mem_Ioc]
  omega

/-- Union bound: at most `∑_{a ∈ A} ⌊x / a⌋` integers in `{1, …, x}` are sieved out. -/
lemma card_sieved_le_sum_div (A : Finset ℕ) (x : ℕ) :
    #{m ∈ Icc 1 x | ∃ a ∈ A, a ∣ m} ≤ ∑ a ∈ A, x / a := by
  classical
  have hEq :
      (Icc 1 x).filter (fun m => ∃ a ∈ A, a ∣ m) =
        A.biUnion fun a => (Icc 1 x).filter (a ∣ ·) := by
    ext m
    simp only [mem_filter, mem_biUnion, mem_Icc]
    tauto
  rw [hEq]
  simpa [card_Icc_filter_dvd] using
    (card_biUnion_le : (A.biUnion fun a => (Icc 1 x).filter (a ∣ ·)).card ≤
      ∑ a ∈ A, ((Icc 1 x).filter (a ∣ ·)).card)

/-- Survivors are `{1, …, x}` minus the sieved set. -/
lemma avoidsDivisors_eq_sdiff (A : Finset ℕ) (x : ℕ) :
    avoidsDivisors A x = Icc 1 x \ (Icc 1 x).filter (fun m => ∃ a ∈ A, a ∣ m) := by
  classical
  ext m
  simp only [mem_avoidsDivisors, mem_sdiff, mem_filter]
  constructor
  · rintro ⟨hm, hA⟩
    exact ⟨hm, fun h ↦ (h.2.elim fun a ⟨ha, hd⟩ ↦ hA a ha hd)⟩
  · rintro ⟨hm, hs⟩
    exact ⟨hm, fun a ha hd ↦ hs ⟨hm, a, ha, hd⟩⟩

/-- Cardinality lower bound via the union bound on multiples. -/
lemma card_avoidsDivisors_add_sum_div_ge (A : Finset ℕ) (x : ℕ) :
    x ≤ (avoidsDivisors A x).card + ∑ a ∈ A, x / a := by
  classical
  have hcard : (Icc 1 x).card = x := by simp [Nat.card_Icc]
  have hsieved := card_sieved_le_sum_div A x
  have hsle : #{m ∈ Icc 1 x | ∃ a ∈ A, a ∣ m} ≤ x :=
    (card_le_card (filter_subset _ _)).trans (by simp [Nat.card_Icc])
  have hsplit :
      (avoidsDivisors A x).card = x - #{m ∈ Icc 1 x | ∃ a ∈ A, a ∣ m} := by
    rw [avoidsDivisors_eq_sdiff, card_sdiff_of_subset (filter_subset _ _), hcard]
  omega

/-- Growing the range can only add survivors. -/
lemma avoidsDivisors_mono_right (A : Finset ℕ) {x y : ℕ} (h : x ≤ y) :
    avoidsDivisors A x ⊆ avoidsDivisors A y := by
  intro m hm
  simp only [mem_avoidsDivisors, mem_Icc] at hm ⊢
  exact ⟨⟨hm.1.1, hm.1.2.trans h⟩, hm.2⟩

/-- Growing the range does not decrease the number of survivors. -/
lemma card_avoidsDivisors_mono_right (A : Finset ℕ) {x y : ℕ} (h : x ≤ y) :
    (avoidsDivisors A x).card ≤ (avoidsDivisors A y).card :=
  card_le_card (avoidsDivisors_mono_right A h)


/-- Sieving by a singleton `{a}` removes exactly the multiples of `a`. -/
lemma avoidsDivisors_singleton (a x : ℕ) :
    avoidsDivisors {a} x = (Icc 1 x).filter (fun m => ¬ a ∣ m) := by
  ext m
  simp [mem_avoidsDivisors]

/-- Cardinality after sieving by a single `a`: `x - ⌊x / a⌋`. -/
lemma card_avoidsDivisors_singleton (a x : ℕ) :
    (avoidsDivisors {a} x).card = x - x / a := by
  classical
  have hsub : (Icc 1 x).filter (a ∣ ·) ⊆ Icc 1 x := filter_subset _ _
  have hEq :
      (Icc 1 x).filter (fun m => ∃ b ∈ ({a} : Finset ℕ), b ∣ m) =
        (Icc 1 x).filter (a ∣ ·) := by
    ext m
    simp
  rw [avoidsDivisors_eq_sdiff, hEq, card_sdiff_of_subset hsub, Nat.card_Icc,
    card_Icc_filter_dvd]
  omega

/-- If `∑_{a ∈ A} 1/a ≤ C`, then at least `(1 - C) x` integers in `{1, …, x}` survive. -/
lemma le_card_avoidsDivisors_of_reciprocalSum_le (A : Finset ℕ) (x : ℕ) {C : ℝ}
    (hC : A.reciprocalSum ≤ C) :
    (1 - C) * (x : ℝ) ≤ (avoidsDivisors A x).card := by
  have hge := card_avoidsDivisors_add_sum_div_ge A x
  have hcast : (x : ℝ) ≤ (avoidsDivisors A x).card + ∑ a ∈ A, ((x / a : ℕ) : ℝ) := by
    exact_mod_cast hge
  have hdiv : ∑ a ∈ A, ((x / a : ℕ) : ℝ) ≤ ∑ a ∈ A, (x : ℝ) / a := by
    gcongr
    exact Nat.cast_div_le
  have hsum : ∑ a ∈ A, (x : ℝ) / a = (x : ℝ) * A.reciprocalSum := by
    simp only [reciprocalSum]
    have hterm : ∀ a ∈ A, (x : ℝ) / a = x * ((1 : ℝ) / a) := fun a _ ↦
      (mul_one_div (x : ℝ) (a : ℝ)).symm
    simp only [sum_congr rfl hterm, ← mul_sum]
  have hmul : (1 - C) * (x : ℝ) ≤ (1 - A.reciprocalSum) * x :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hrewrite : (1 - A.reciprocalSum) * (x : ℝ) = x - x * A.reciprocalSum := by
    rw [sub_mul, one_mul, mul_comm A.reciprocalSum]
  have hchain : x - ∑ a ∈ A, (x : ℝ) / a ≤ (avoidsDivisors A x).card := by
    linarith
  calc (1 - C) * (x : ℝ)
      ≤ (1 - A.reciprocalSum) * x := hmul
    _ = x - x * A.reciprocalSum := hrewrite
    _ = x - ∑ a ∈ A, (x : ℝ) / a := by rw [hsum]
    _ ≤ (avoidsDivisors A x).card := hchain


/-- Enlarging the divisor set does not increase the number of survivors. -/
lemma card_avoidsDivisors_mono_left {A B : Finset ℕ} (h : A ⊆ B) (x : ℕ) :
    (avoidsDivisors B x).card ≤ (avoidsDivisors A x).card :=
  card_le_card (avoidsDivisors_mono h x)

/-- Divisors strictly larger than `x` never divide any `m ∈ {1, …, x}`. -/
lemma not_dvd_of_mem_Icc_of_lt {a m x : ℕ} (hm : m ∈ Icc 1 x) (ha : x < a) : ¬ a ∣ m := by
  intro hdvd
  have hpos : 0 < m := by
    have : 1 ≤ m := (mem_Icc.mp hm).1
    omega
  have : a ≤ m := Nat.le_of_dvd hpos hdvd
  have : m ≤ x := (mem_Icc.mp hm).2
  omega

/-- Only divisors `≤ x` affect the sieve on `{1, …, x}`. -/
lemma avoidsDivisors_eq_avoidsDivisors_filter_le (A : Finset ℕ) (x : ℕ) :
    avoidsDivisors A x = avoidsDivisors (A.filter (· ≤ x)) x := by
  ext m
  simp only [mem_avoidsDivisors, mem_filter]
  constructor
  · rintro ⟨hm, hA⟩
    exact ⟨hm, fun a ha ↦ hA a ha.1⟩
  · rintro ⟨hm, hA⟩
    refine ⟨hm, fun a ha hdvd ↦ ?_⟩
    by_cases hle : a ≤ x
    · exact hA a ⟨ha, hle⟩ hdvd
    · exact not_dvd_of_mem_Icc_of_lt hm (lt_of_not_ge hle) hdvd

/-- Same survivor count after discarding divisors `> x`. -/
lemma card_avoidsDivisors_filter_le (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors (A.filter (· ≤ x)) x).card = (avoidsDivisors A x).card := by
  rw [← avoidsDivisors_eq_avoidsDivisors_filter_le]

/-- Inserting a useless divisor (`> x`) does not change the survivor set. -/
lemma avoidsDivisors_insert_of_lt {A : Finset ℕ} {a x : ℕ} (ha : x < a) :
    avoidsDivisors (insert a A) x = avoidsDivisors A x := by
  classical
  have h : (insert a A).filter (· ≤ x) = A.filter (· ≤ x) := by
    ext m
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hm, hle⟩
      · omega
      · exact ⟨hm, hle⟩
    · rintro ⟨hm, hle⟩
      exact ⟨Or.inr hm, hle⟩
  calc
    avoidsDivisors (insert a A) x = avoidsDivisors ((insert a A).filter (· ≤ x)) x :=
      avoidsDivisors_eq_avoidsDivisors_filter_le _ _
    _ = avoidsDivisors (A.filter (· ≤ x)) x := by rw [h]
    _ = avoidsDivisors A x := (avoidsDivisors_eq_avoidsDivisors_filter_le A x).symm



/-- Survivors always lie in `{1, …, x}`. -/
lemma avoidsDivisors_subset (A : Finset ℕ) (x : ℕ) :
    avoidsDivisors A x ⊆ Icc 1 x :=
  filter_subset _ _

/-- In particular the survivor count is at most `x`. -/
lemma card_avoidsDivisors_le_self (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors A x).card ≤ x := by
  simpa [Nat.card_Icc] using card_le_card (avoidsDivisors_subset A x)

/-- `1` is never a member of `{2, …, x}`. -/
lemma one_not_mem_of_subset_Icc_two {A : Finset ℕ} {x : ℕ} (hA : A ⊆ Icc 2 x) :
    1 ∉ A := by
  intro h
  have := mem_Icc.mp (hA h)
  omega

/-- If `1 ∉ A` and `x ≥ 1`, then `1` survives the sieve (nothing in `A` divides `1`). -/
lemma one_mem_avoidsDivisors {A : Finset ℕ} {x : ℕ} (hx : 1 ≤ x) (h1 : 1 ∉ A) :
    1 ∈ avoidsDivisors A x := by
  refine mem_avoidsDivisors.mpr ⟨mem_Icc.mpr ⟨le_rfl, hx⟩, ?_⟩
  intro a ha hdvd
  exact h1 ((Nat.dvd_one.mp hdvd) ▸ ha)

/-- Hence the survivor set is nonempty whenever `x ≥ 1` and `1 ∉ A`. -/
lemma one_le_card_avoidsDivisors {A : Finset ℕ} {x : ℕ} (hx : 1 ≤ x) (h1 : 1 ∉ A) :
    1 ≤ (avoidsDivisors A x).card :=
  Finset.card_pos.mpr ⟨1, one_mem_avoidsDivisors hx h1⟩

/-- The sieve empties `{1, …, x}` precisely when the range is empty or `1` is a divisor. -/
lemma avoidsDivisors_eq_empty_iff (A : Finset ℕ) (x : ℕ) :
    avoidsDivisors A x = ∅ ↔ x = 0 ∨ 1 ∈ A := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · refine Or.inr ?_
      have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
      by_contra h1
      have : 1 ∈ avoidsDivisors A x := one_mem_avoidsDivisors hx1 h1
      simp [h] at this
  · rintro (rfl | h1)
    · simp [avoidsDivisors, Icc_eq_empty_of_lt]
    · exact avoidsDivisors_eq_empty_of_one_mem h1 x

/-- Same characterisation in terms of cardinality. -/
lemma card_avoidsDivisors_eq_zero_iff (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors A x).card = 0 ↔ x = 0 ∨ 1 ∈ A := by
  rw [card_eq_zero, avoidsDivisors_eq_empty_iff]

/-- Explicit survivor count: range size minus the number of multiples of some `a ∈ A`. -/
lemma card_avoidsDivisors_eq_sub_sieved (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors A x).card = x - #{m ∈ Icc 1 x | ∃ a ∈ A, a ∣ m} := by
  classical
  rw [avoidsDivisors_eq_sdiff, card_sdiff_of_subset (filter_subset _ _), Nat.card_Icc]
  omega

/-- Nat form of the union bound: at least `x - ∑ ⌊x/a⌋` survivors. -/
lemma le_card_avoidsDivisors_sub_sum_div (A : Finset ℕ) (x : ℕ) :
    x - ∑ a ∈ A, x / a ≤ (avoidsDivisors A x).card :=
  Nat.sub_le_iff_le_add.mpr (card_avoidsDivisors_add_sum_div_ge A x)

/-- Inserting a divisor keeps only those previous survivors not divisible by it. -/
lemma avoidsDivisors_insert (A : Finset ℕ) (a x : ℕ) :
    avoidsDivisors (insert a A) x = (avoidsDivisors A x).filter (fun m => ¬ a ∣ m) := by
  ext m
  simp only [mem_avoidsDivisors, mem_filter, mem_insert]
  constructor
  · rintro ⟨hm, hA⟩
    exact ⟨⟨hm, fun b hb ↦ hA b (Or.inr hb)⟩, hA a (Or.inl rfl)⟩
  · rintro ⟨⟨hm, hA⟩, ha⟩
    refine ⟨hm, fun b hb ↦ ?_⟩
    rcases hb with rfl | hb
    · exact ha
    · exact hA b hb

/-- `0` never divides a positive integer, so zeros in the sieve are irrelevant on `{1, …, x}`. -/
lemma avoidsDivisors_eq_avoidsDivisors_filter_ne_zero (A : Finset ℕ) (x : ℕ) :
    avoidsDivisors A x = avoidsDivisors (A.filter (· ≠ 0)) x := by
  ext m
  simp only [mem_avoidsDivisors, mem_filter]
  constructor
  · rintro ⟨hm, hA⟩
    exact ⟨hm, fun a ha ↦ hA a ha.1⟩
  · rintro ⟨hm, hA⟩
    refine ⟨hm, fun a ha hdvd ↦ ?_⟩
    by_cases hz : a = 0
    · have hpos : 0 < m := by
        have : 1 ≤ m := (mem_Icc.mp hm).1
        omega
      have : m = 0 := Nat.eq_zero_of_zero_dvd (by simpa [hz] using hdvd)
      omega
    · exact hA a ⟨ha, hz⟩ hdvd

/-- Same survivor count after discarding zeros from the sieve. -/
lemma card_avoidsDivisors_filter_ne_zero (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors (A.filter (· ≠ 0)) x).card = (avoidsDivisors A x).card := by
  rw [← avoidsDivisors_eq_avoidsDivisors_filter_ne_zero]

/-- Including `a` in the sieve can only shrink survivors relative to sieving by `{a}`. -/
lemma avoidsDivisors_subset_avoidsDivisors_singleton {A : Finset ℕ} {a x : ℕ}
    (ha : a ∈ A) :
    avoidsDivisors A x ⊆ avoidsDivisors {a} x :=
  avoidsDivisors_mono (singleton_subset_iff.mpr ha) x

/-- Hence `#survivors ≤ x - ⌊x/a⌋` whenever `a ∈ A`. -/
lemma card_avoidsDivisors_le_sub_div_of_mem {A : Finset ℕ} {a x : ℕ}
    (ha : a ∈ A) :
    (avoidsDivisors A x).card ≤ x - x / a := by
  simpa [card_avoidsDivisors_singleton] using
    card_le_card (avoidsDivisors_subset_avoidsDivisors_singleton (a := a) ha)


/-- If every sieve element exceeds `x`, nothing in `{1, …, x}` is hit. -/
lemma avoidsDivisors_eq_Icc_of_forall_lt {A : Finset ℕ} {x : ℕ}
    (hA : ∀ a ∈ A, x < a) : avoidsDivisors A x = Icc 1 x := by
  classical
  have hfilt : A.filter (· ≤ x) = ∅ :=
    filter_eq_empty_iff.mpr fun a ha ↦ not_le_of_gt (hA a ha)
  calc
    avoidsDivisors A x = avoidsDivisors (A.filter (· ≤ x)) x :=
      avoidsDivisors_eq_avoidsDivisors_filter_le _ _
    _ = avoidsDivisors ∅ x := by rw [hfilt]
    _ = Icc 1 x := avoidsDivisors_empty x

/-- Hence the survivor count is `x` when every sieve element exceeds `x`. -/
lemma card_avoidsDivisors_eq_of_forall_lt {A : Finset ℕ} {x : ℕ}
    (hA : ∀ a ∈ A, x < a) : (avoidsDivisors A x).card = x := by
  simp [avoidsDivisors_eq_Icc_of_forall_lt hA, Nat.card_Icc]

end Finset
