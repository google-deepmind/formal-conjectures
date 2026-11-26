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

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
# Sets avoiding unit-fraction pairs

*References:*
- [erdosproblems.com/327](https://www.erdosproblems.com/327)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique (1980).

Divisibility conditions for sums of two reciprocals, the odd-number baseline,
and an elementary cardinality bound for Erdős Problem 327.
-/

@[expose] public section

namespace Erdos327

/-- `A` satisfies the first condition: `a + b ∤ a b` for all distinct `a, b ∈ A`. -/
def Admissible1 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ (a + b ∣ a * b)

/-- `A` satisfies the second condition: `a + b ∤ 2 a b` for all distinct `a, b ∈ A`. -/
def Admissible2 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ (a + b ∣ 2 * a * b)

/-! ## Proved elementary results -/

/-- The observation on the problem page: for positive integers `a, b`,
`1/a + 1/b` is a unit fraction iff `a + b ∣ a b`. -/
theorem unit_fraction_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∃ k : ℕ, (1 : ℚ) / a + 1 / b = 1 / k) ↔ a + b ∣ a * b := by
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hb' : (b : ℚ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      rw [h, div_zero] at hk
      have : (0 : ℚ) < 1 / a + 1 / b := by positivity
      linarith
    refine ⟨k, ?_⟩
    field_simp at hk
    exact_mod_cast (by linarith : (a : ℚ) * b = (a + b) * k)
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : (a : ℚ) * b = (a + b) * k := by exact_mod_cast hk
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hk'
      exact mul_ne_zero ha' hb' hk'
    field_simp
    linarith

/-- The second condition implies the first (`a + b ∣ ab → a + b ∣ 2ab`). -/
theorem Admissible2.admissible1 {A : Finset ℕ} (h : Admissible2 A) : Admissible1 A := by
  intro a ha b hb hab hdvd
  exact h a ha b hb hab (by rw [mul_assoc]; exact Dvd.dvd.mul_left hdvd 2)

/-- The odd numbers in `{1,…,N}`. -/
def oddsUpTo (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter Odd

/-- The odd numbers satisfy the first condition. -/
theorem oddsUpTo_admissible1 (N : ℕ) : Admissible1 (oddsUpTo N) := by
  intro a ha b hb _ hdvd
  simp only [oddsUpTo, Finset.mem_filter] at ha hb
  have heven : Even (a + b) := Odd.add_odd ha.2 hb.2
  have hodd : Odd (a * b) := Odd.mul ha.2 hb.2
  exact (Nat.not_even_iff_odd.mpr hodd) (heven.two_dvd.trans hdvd |> even_iff_two_dvd.mpr)

/-- There are `⌈N/2⌉ = (N+1)/2` odd numbers in `{1,…,N}`. -/
theorem card_oddsUpTo (N : ℕ) : (oddsUpTo N).card = (N + 1) / 2 := by
  have : oddsUpTo N = (Finset.range ((N + 1) / 2)).image (fun i => 2 * i + 1) := by
    ext n
    simp only [oddsUpTo, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range, Nat.odd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨n / 2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun i j h => by simpa using h)]
  simp

/-- Baseline: for every `N` there is a set satisfying the first condition of size
`⌈N/2⌉` (the odd numbers). -/
theorem exists_admissible1_half (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible1 A ∧ A.card = (N + 1) / 2 :=
  ⟨oddsUpTo N, Finset.filter_subset _ _, oddsUpTo_admissible1 N, card_oddsUpTo N⟩

/-- The odd numbers do *not* satisfy the second condition once `N ≥ 15`:
`3 + 15 = 18 ∣ 90 = 2·3·15`. -/
theorem oddsUpTo_not_admissible2 {N : ℕ} (hN : 15 ≤ N) : ¬ Admissible2 (oddsUpTo N) := by
  intro h
  refine h 3 ?_ 15 ?_ (by norm_num) (by norm_num) <;>
    simp only [oddsUpTo, Finset.mem_filter, Finset.mem_Icc] <;>
    refine ⟨⟨by norm_num, by omega⟩, by decide⟩

/-- The map `6m ↦ 3m` for odd `m` (i.e. on `n ≡ 6 mod 12`), identity elsewhere. -/
def halveSix (n : ℕ) : ℕ := if n % 12 = 6 then n / 2 else n

/-- Elementary upper bound: a set `A ⊆ {1,…,N}` satisfying the first condition misses at
least one element of each of the disjoint pairs `{3m, 6m}` (`m` odd, `6m ≤ N`), because
`3m + 6m = 9m ∣ 18m² = 3m·6m`. Hence `|A| + ⌊(⌊N/6⌋ + 1)/2⌋ ≤ N`. -/
theorem card_add_le_of_admissible1 {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hadm : Admissible1 A) : A.card + (N / 6 + 1) / 2 ≤ N := by
  set D : Finset ℕ := (Finset.range ((N / 6 + 1) / 2)).image (fun j => 6 * (2 * j + 1))
    with hD
  have hDcard : D.card = (N / 6 + 1) / 2 := by
    rw [hD, Finset.card_image_of_injective _ (fun i j h => by simp at h; omega)]
    simp
  have hDsub : D ⊆ Finset.Icc 1 N := by
    intro x hx
    simp only [hD, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    omega
  have hDmod : ∀ x ∈ D, x % 12 = 6 := by
    intro x hx
    simp only [hD, Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    omega
  -- conflict between `y` and `2y` when `y ≡ 3 mod 6`
  have hconf : ∀ x y : ℕ, x % 12 = 6 → y = x / 2 → x + y ∣ x * y := by
    intro x y hx hy
    obtain ⟨t, rfl⟩ : 3 ∣ y := by omega
    have hx' : x = 6 * t := by omega
    subst hx'
    exact ⟨2 * t, by ring⟩
  have hinj : Set.InjOn halveSix (A : Set ℕ) := by
    intro x hx y hy hxy
    simp only [halveSix] at hxy
    by_contra hne
    split_ifs at hxy with h1 h2 h2
    · omega
    · exact hadm x hx y hy hne (hconf x y h1 hxy.symm)
    · exact hadm x hx y hy hne (by
        rw [add_comm, mul_comm]; exact hconf y x h2 hxy)
    · exact hne hxy
  have himg : A.image halveSix ⊆ Finset.Icc 1 N \ D := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxI := Finset.mem_Icc.mp (hA hx)
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    simp only [halveSix]
    split_ifs with h
    · exact ⟨⟨by omega, by omega⟩, fun hm => by have := hDmod _ hm; omega⟩
    · exact ⟨hxI, fun hm => h (hDmod _ hm)⟩
  have h1 := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset hDsub,
    Nat.card_Icc, hDcard] at h1
  have : (N / 6 + 1) / 2 ≤ N := by omega
  omega

/-- The same elementary upper bound for the second condition. -/
theorem card_add_le_of_admissible2 {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hadm : Admissible2 A) : A.card + (N / 6 + 1) / 2 ≤ N :=
  card_add_le_of_admissible1 hA hadm.admissible1

end Erdos327
