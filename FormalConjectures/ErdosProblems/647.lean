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
# Erdős Problem 647

*Reference:* [erdosproblems.com/647](https://www.erdosproblems.com/647)
-/

namespace Erdos647

open Filter ArithmeticFunction.sigma

/-- A natural number satisfies the condition in Erdős Problem 647. -/
def Candidate (n : ℕ) : Prop :=
  24 < n ∧ ⨆ m : Fin n, (m : ℕ) + σ 0 m ≤ n + 2

/-- The candidate API unfolds to the exact expression in the open theorem. -/
@[category API, AMS 11]
theorem candidate_iff_open_expression (n : ℕ) :
    Candidate n ↔
      24 < n ∧ ⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m ≤ n + 2 :=
  Iff.rfl

/-- The finite set of candidates for Erdős Problem 647 up to $X$. -/
noncomputable def candidatesUpTo (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter Candidate

/-- The candidates up to $X$ that are large enough for the campaign's reduction theorems. -/
noncomputable def largeCandidatesUpTo (X : ℕ) : Finset ℕ := by
  classical
  exact (candidatesUpTo X).filter (84 < ·)

/-- Membership in the bounded candidate set. -/
@[category API, AMS 11]
theorem mem_candidatesUpTo {X n : ℕ} :
    n ∈ candidatesUpTo X ↔ 1 ≤ n ∧ n ≤ X ∧ Candidate n := by
  classical
  simp [candidatesUpTo, and_assoc]

/-- Membership restated without project-local abbreviations, for compatibility checks. -/
@[category API, AMS 11]
theorem mem_candidatesUpTo_open_expression {X n : ℕ} :
    n ∈ candidatesUpTo X ↔
      1 ≤ n ∧ n ≤ X ∧ 24 < n ∧
        (⨆ m : Fin n,
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  classical
  simp [candidatesUpTo, Candidate, and_assoc]

/-- Membership in the bounded set of candidates larger than $84$. -/
@[category API, AMS 11]
theorem mem_largeCandidatesUpTo {X n : ℕ} :
    n ∈ largeCandidatesUpTo X ↔ 1 ≤ n ∧ n ≤ X ∧ Candidate n ∧ 84 < n := by
  classical
  simp [largeCandidatesUpTo, mem_candidatesUpTo, and_assoc]

/-- Removing the finite interval $25 \leq n \leq 84$ loses at most $60$ candidates. -/
@[category API, AMS 11]
theorem card_candidatesUpTo_le_add_card_largeCandidatesUpTo (X : ℕ) :
    (candidatesUpTo X).card ≤ 60 + (largeCandidatesUpTo X).card := by
  classical
  let small := (candidatesUpTo X).filter fun n => ¬84 < n
  have hsmall_subset : small ⊆ Finset.Icc 25 84 := by
    intro n hn
    simp only [small, Finset.mem_filter] at hn
    have hcand := (mem_candidatesUpTo.mp hn.1).2.2
    have hn24 : 24 < n := hcand.1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsmall : small.card ≤ 60 := by
    calc
      small.card ≤ (Finset.Icc 25 84).card := Finset.card_le_card hsmall_subset
      _ = 60 := by norm_num [Nat.card_Icc]
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := candidatesUpTo X) (fun n => 84 < n)
  rw [← largeCandidatesUpTo] at hpartition
  change (largeCandidatesUpTo X).card + small.card = (candidatesUpTo X).card at hpartition
  omega

/-- Every candidate is greater than $24$. -/
@[category API, AMS 11]
theorem Candidate.twenty_four_lt {n : ℕ} (hn : Candidate n) : 24 < n :=
  hn.1

/-- Every candidate satisfies the divisor-count bound from Erdős Problem 647. -/
@[category API, AMS 11]
theorem Candidate.bound {n : ℕ} (hn : Candidate n) :
    ⨆ m : Fin n, (m : ℕ) + σ 0 m ≤ n + 2 :=
  hn.2

/-- The candidate bound is equivalently an upper bound of two on the
translated maximum used in the limit variant. -/
@[category API, AMS 11]
theorem candidate_iff_excess_le_two (n : ℕ) :
    Candidate n ↔
      24 < n ∧ (⨆ m : Fin n, σ 0 m + m - n) ≤ 2 := by
  rw [Candidate]
  constructor
  · rintro ⟨hn24, hmax⟩
    refine ⟨hn24, ?_⟩
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    apply ciSup_le
    intro m
    let f : Fin n → ℕ := fun i ↦ (i : ℕ) + σ 0 i
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨i, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (i : ℕ)
      have hi : (i : ℕ) < n := i.isLt
      omega
    have hm : (m : ℕ) + σ 0 m ≤ n + 2 :=
      (le_ciSup hbdd m).trans hmax
    omega
  · rintro ⟨hn24, hexcess⟩
    refine ⟨hn24, ?_⟩
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    apply ciSup_le
    intro m
    let g : Fin n → ℕ := fun i ↦ σ 0 i + (i : ℕ) - n
    have hbdd : BddAbove (Set.range g) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨i, rfl⟩
      dsimp [g]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (i : ℕ)
      have hi : (i : ℕ) < n := i.isLt
      omega
    have hm : σ 0 m + (m : ℕ) - n ≤ 2 :=
      (le_ciSup hbdd m).trans hexcess
    omega

/-- `n` satisfies every pointwise divisor-count budget through shift depth `D`. -/
def SurvivesThrough (n D : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ D → k < n → σ 0 (n - k) ≤ k + 2

/-- The global maximum condition is exactly equivalent to all positive shift budgets. -/
@[category API, AMS 11]
theorem full_max_iff_shift_budgets (n : ℕ) :
    ((⨆ m : Fin n, (m : ℕ) + σ 0 m) ≤ n + 2 ↔
      ∀ k : ℕ, 0 < k → k < n → σ 0 (n - k) ≤ k + 2) := by
  constructor
  · intro H k hk0 hkn
    let f : Fin n → ℕ := fun x => (x : ℕ) + σ 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, by omega⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  · intro H
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
      apply ciSup_le
      intro m
      by_cases hm0 : (m : ℕ) = 0
      · have hs0 : σ 0 (m : ℕ) = 0 := by
          rw [hm0]
          native_decide
        omega
      · let k := n - (m : ℕ)
        have hk0 : 0 < k := by
          dsimp [k]
          omega
        have hkn : k < n := by
          dsimp [k]
          omega
        have hk := H k hk0 hkn
        have hnkm : n - k = (m : ℕ) := by
          dsimp [k]
          omega
        rw [hnkm] at hk
        omega

/-- Candidacy is exactly being above `24` and surviving every available shift. -/
@[category API, AMS 11]
theorem candidate_iff_full_depth_survivor (n : ℕ) :
    Candidate n ↔ 24 < n ∧ SurvivesThrough n (n - 1) := by
  rw [Candidate, full_max_iff_shift_budgets]
  constructor
  · rintro ⟨hn24, H⟩
    exact ⟨hn24, fun k hk0 _ hkn => H k hk0 hkn⟩
  · rintro ⟨hn24, H⟩
    exact ⟨hn24, fun k hk0 hkn => H k hk0 (by omega) hkn⟩

/-- Above `24`, non-candidacy is exactly witnessed by one failed shift budget. -/
@[category API, AMS 11]
theorem not_candidate_iff_exists_shift_failure {n : ℕ} (hn : 24 < n) :
    ¬Candidate n ↔
      ∃ k : ℕ, 0 < k ∧ k < n ∧ k + 2 < σ 0 (n - k) := by
  simp only [Candidate, hn, true_and]
  rw [full_max_iff_shift_budgets]
  push Not
  rfl

/-- Every number from `25` through `84` has a concrete failed shift budget. -/
@[category API, AMS 11]
theorem finite_band_has_shift_failure :
    ∀ n ∈ Finset.Icc 25 84,
      ∃ k ∈ Finset.Icc 1 (n - 1), k + 2 < σ 0 (n - k) := by
  native_decide

/-- There is no candidate in the finite interval `25 ≤ n ≤ 84`. -/
@[category API, AMS 11]
theorem no_candidate_in_finite_band :
    ∀ n : ℕ, 24 < n → n ≤ 84 → ¬Candidate n := by
  intro n hn24 hn84
  rw [not_candidate_iff_exists_shift_failure hn24]
  obtain ⟨k, hk, hkfail⟩ :=
    finite_band_has_shift_failure n (Finset.mem_Icc.mpr ⟨by omega, hn84⟩)
  have hk_bounds := Finset.mem_Icc.mp hk
  exact ⟨k, by omega, by omega, hkfail⟩

/-- Every hypothetical candidate is therefore larger than `84`. -/
@[category API, AMS 11]
theorem Candidate.eighty_four_lt {n : ℕ} (hn : Candidate n) : 84 < n := by
  by_contra h
  exact no_candidate_in_finite_band n hn.twenty_four_lt (by omega) hn

/-- Nonexistence is exactly the remaining large-range failed-shift obligation. -/
@[category API, AMS 11]
theorem no_candidates_iff_all_large_have_shift_failure :
    (∀ n : ℕ, ¬Candidate n) ↔
      ∀ n : ℕ, 84 < n →
        ∃ k : ℕ, 0 < k ∧ k < n ∧ k + 2 < σ 0 (n - k) := by
  constructor
  · intro H n hn84
    exact (not_candidate_iff_exists_shift_failure (by omega)).mp (H n)
  · intro H n hn
    by_cases hn84 : 84 < n
    · exact ((not_candidate_iff_exists_shift_failure hn.twenty_four_lt).mpr
        (H n hn84)) hn
    · exact (no_candidate_in_finite_band n hn.twenty_four_lt (by omega)) hn

/-- Every candidate survives the pointwise shift budgets through every finite depth. -/
@[category API, AMS 11]
theorem Candidate.survivesThrough {n : ℕ} (hn : Candidate n) (D : ℕ) :
    SurvivesThrough n D := by
  intro k hk0 _ hkn
  let f : Fin n → ℕ := fun x => (x : ℕ) + σ 0 x
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨2 * n, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [f]
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    omega
  let m : Fin n := ⟨n - k, by omega⟩
  have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) hn.bound
  dsimp [f, m] at hm
  omega

/-- A failed pointwise budget at any depth rules out candidacy. -/
@[category API, AMS 11]
theorem not_candidate_of_depth_failure {n D : ℕ}
    (hfail : ∃ k : ℕ, 0 < k ∧ k ≤ D ∧ k < n ∧ k + 2 < σ 0 (n - k)) :
    ¬Candidate n := by
  intro hn
  obtain ⟨k, hk0, hkD, hkn, hkfail⟩ := hfail
  have hk := hn.survivesThrough D k hk0 hkD hkn
  omega

/-- A short-window maximum bound is exactly the corresponding finite family
of pointwise shift budgets. -/
@[category API, AMS 11]
theorem window_iff_shift_budgets (n k : ℕ) :
    ((⨆ m : Set.Ioo (n - k) n,
        (m : ℕ) + σ 0 m) ≤ n + 2) ↔
      ∀ j : ℕ, 0 < j → j ≤ k - 1 → j < n →
        σ 0 (n - j) ≤ j + 2 := by
  constructor
  · intro H j hj0 hjk hjn
    let g : Set.Ioo (n - k) n → ℕ := fun m =>
      (m : ℕ) + σ 0 m
    have hbdd : BddAbove (Set.range g) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [g]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.property.2
      omega
    have hjk' : j < k := by omega
    let m : Set.Ioo (n - k) n :=
      ⟨n - j, by constructor <;> omega⟩
    have hm : g m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [g, m] at hm
    omega
  · intro H
    apply ciSup_le'
    intro m
    have hmlo : n - k < (m : ℕ) := m.property.1
    have hmhi : (m : ℕ) < n := m.property.2
    let j := n - (m : ℕ)
    have hj0 : 0 < j := by dsimp [j]; omega
    have hjk : j ≤ k - 1 := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hs := H j hj0 hjk hjn
    have hsubeq : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    dsimp [j] at hs
    rw [hsubeq] at hs
    omega

/-- The infinite-window statement is exactly infinitude of the survivor set
at every fixed shift depth. -/
@[category API, AMS 11]
theorem infinite_windows_iff_shift_survivors :
    (∀ k : ℕ,
      {n | (⨆ m : Set.Ioo (n - k) n,
        (m : ℕ) + σ 0 m) ≤ n + 2}.Infinite) ↔
    ∀ k : ℕ, {n | SurvivesThrough n (k - 1)}.Infinite := by
  constructor
  · intro H k
    have hset :
        {n | (⨆ m : Set.Ioo (n - k) n,
          (m : ℕ) + σ 0 m) ≤ n + 2} =
        {n | SurvivesThrough n (k - 1)} := by
      ext n
      exact window_iff_shift_budgets n k
    rw [← hset]
    exact H k
  · intro H k
    have hset :
        {n | (⨆ m : Set.Ioo (n - k) n,
          (m : ℕ) + σ 0 m) ≤ n + 2} =
        {n | SurvivesThrough n (k - 1)} := by
      ext n
      exact window_iff_shift_budgets n k
    rw [hset]
    exact H k

/-- The infinite-window assertion is unconditional for window sizes at most
two.  The first genuinely open size is three. -/
@[category API, AMS 11]
theorem infinite_windows_up_to_two :
    ∀ k : ℕ, k ≤ 2 →
      {n | (⨆ m : Set.Ioo (n - k) n,
        (m : ℕ) + σ 0 m) ≤ n + 2}.Infinite := by
  intro k hk
  have hsurv : {n : ℕ | SurvivesThrough n (k - 1)}.Infinite := by
    by_cases hk2 : k = 2
    · subst k
      have hprime : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOf_prime
      have hinj : Set.InjOn (fun p : ℕ ↦ p + 1) {p : ℕ | p.Prime} := by
        intro a _ b _ hab
        exact Nat.add_right_cancel hab
      have himage : ((fun p : ℕ ↦ p + 1) '' {p : ℕ | p.Prime}).Infinite :=
        (Set.infinite_image_iff hinj).2 hprime
      apply himage.mono
      rintro n ⟨p, hp, rfl⟩
      intro j hj0 hjD hjn
      have hj : j = 1 := by omega
      subst j
      have hsigma : σ 0 p = 2 := by
        simpa using
          (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hp)
      simp [hsigma]
    · have hk1 : k ≤ 1 := by omega
      have hall : {n : ℕ | SurvivesThrough n (k - 1)} = Set.univ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro j hj0 hjD
        omega
      rw [hall]
      exact Set.infinite_univ
  have hset :
      {n | (⨆ m : Set.Ioo (n - k) n,
        (m : ℕ) + σ 0 m) ≤ n + 2} =
      {n | SurvivesThrough n (k - 1)} := by
    ext n
    exact window_iff_shift_budgets n k
  rw [hset]
  exact hsurv

/-- Infinitely many Sophie Germain primes would settle the first open window
size, namely `k = 3`. -/
@[category API, AMS 11]
theorem infinite_window_three_of_infinite_sophie_germain
    (hsafe : {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Infinite) :
    {n | (⨆ m : Set.Ioo (n - 3) n,
      (m : ℕ) + σ 0 m) ≤ n + 2}.Infinite := by
  have hinj : Set.InjOn (fun q : ℕ ↦ 2 * q + 2)
      {q : ℕ | q.Prime ∧ (2 * q + 1).Prime} := by
    intro a _ b _ hab
    have hab' : 2 * a = 2 * b := Nat.add_right_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hab'
  have himage :
      ((fun q : ℕ ↦ 2 * q + 2) ''
        {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Infinite :=
    (Set.infinite_image_iff hinj).2 hsafe
  have hsurv : {n : ℕ | SurvivesThrough n 2}.Infinite := by
    apply himage.mono
    rintro n ⟨q, hq, rfl⟩
    intro j hj0 hj2 hjn
    interval_cases j
    · have hsigma : σ 0 (2 * q + 1) = 2 := by
        simpa using
          (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hq.2)
      have hsub : 2 * q + 2 - 1 = 2 * q + 1 := by omega
      rw [hsub, hsigma]
      norm_num
    · by_cases hq2 : q = 2
      · subst q
        native_decide
      · have hcop : Nat.Coprime 2 q := by
          rw [Nat.prime_two.coprime_iff_not_dvd]
          rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.1]
          exact Ne.symm hq2
        have hmul :=
          (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_mul_of_coprime hcop
        have hs2 : σ 0 2 = 2 := by
          simpa using
            (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) Nat.prime_two)
        have hsq : σ 0 q = 2 := by
          simpa using
            (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hq.1)
        rw [hs2, hsq] at hmul
        norm_num at hmul ⊢
        exact hmul.le
  have hset :
      {n | (⨆ m : Set.Ioo (n - 3) n,
        (m : ℕ) + σ 0 m) ≤ n + 2} =
      {n | SurvivesThrough n 2} := by
    ext n
    simpa using (window_iff_shift_budgets n 3)
  rw [hset]
  exact hsurv

@[category API, AMS 11]
private lemma five_le_card_of_chain_mem {s : Finset ℕ} {a b c d e : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s) :
    5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset ℕ) ⊆ s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb, hc, hd, he⟩
  have hanot : a ∉ ({b, c, d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hbnot : b ∉ ({c, d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hcnot : c ∉ ({d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hdnot : d ∉ ({e} : Finset ℕ) := by
    simpa using ne_of_lt hde
  have hcard : ({a, b, c, d, e} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem hanot,
      Finset.card_insert_of_notMem hbnot,
      Finset.card_insert_of_notMem hcnot,
      Finset.card_insert_of_notMem hdnot,
      Finset.card_singleton]
  rw [← hcard]
  exact Finset.card_le_card hsub

@[category API, AMS 11]
private lemma prime_or_prime_square_of_sigma_zero_le_three {a : ℕ}
    (ha : 1 < a) (htau : σ 0 a ≤ 3) :
    ∃ p : ℕ, p.Prime ∧ (a = p ∨ a = p ^ 2) := by
  have ha0 : a ≠ 0 := by omega
  obtain ⟨p, hp, hpa_dvd⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  by_cases hpa : p = a
  · exact ⟨p, hp, Or.inl hpa.symm⟩
  · have hple : p ≤ a := Nat.le_of_dvd (by omega) hpa_dvd
    have hplt : p < a := lt_of_le_of_ne hple hpa
    have h1mem : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha0
    have hpmem : p ∈ a.divisors := Nat.mem_divisors.mpr ⟨hpa_dvd, ha0⟩
    have hamem : a ∈ a.divisors := Nat.mem_divisors_self a ha0
    have hsubset : ({1, p, a} : Finset ℕ) ⊆ a.divisors := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨h1mem, hpmem, hamem⟩
    have hane1 : a ≠ 1 := by omega
    have htri_card : ({1, p, a} : Finset ℕ).card = 3 := by
      have h1not : 1 ∉ ({p, a} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hp.ne_one, Ne.symm hane1⟩
      have hpnot : p ∉ ({a} : Finset ℕ) := by
        simpa using hpa
      rw [Finset.card_insert_of_notMem h1not,
        Finset.card_insert_of_notMem hpnot, Finset.card_singleton]
    have hcard : a.divisors.card ≤ 3 := by
      rwa [← ArithmeticFunction.sigma_zero_apply]
    have hcardle : a.divisors.card ≤ ({1, p, a} : Finset ℕ).card := by
      rw [htri_card]
      exact hcard
    have hdiv_eq : ({1, p, a} : Finset ℕ) = a.divisors :=
      Finset.eq_of_subset_of_card_le hsubset hcardle
    have hqmem : a / p ∈ a.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hpa_dvd, ha0⟩
    rw [← hdiv_eq] at hqmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
    rcases hqmem with hq1 | hqp | hqa
    · have hmul := Nat.mul_div_cancel' hpa_dvd
      rw [hq1, mul_one] at hmul
      exact (hpa hmul).elim
    · refine ⟨p, hp, Or.inr ?_⟩
      have hmul := Nat.mul_div_cancel' hpa_dvd
      rw [hqp] at hmul
      simpa [pow_two] using hmul.symm
    · have hlt : a / p < a := Nat.div_lt_self (by omega) hp.one_lt
      omega

@[category API, AMS 11]
private lemma four_lt_sigma_zero_prime_square_sub_one {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 < σ 0 (p ^ 2 - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hfactor : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    have halg : (p - 1) * (p + 1) + 1 = p ^ 2 := by
      nlinarith [Nat.sub_add_cancel hp1]
    omega
  have hNpos : 0 < p ^ 2 - 1 := by
    have hpows : 1 < p ^ 2 := by nlinarith
    omega
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp]
    omega
  obtain ⟨t, ht⟩ := Nat.coprime_two_left.mp hcop
  have hpminus : p - 1 = 2 * t := by omega
  have h2dvd : 2 ∣ p ^ 2 - 1 := by
    refine ⟨t * (p + 1), ?_⟩
    rw [← hfactor, hpminus]
    ring
  have hpm_dvd : p - 1 ∣ p ^ 2 - 1 := ⟨p + 1, hfactor.symm⟩
  have hpp_dvd : p + 1 ∣ p ^ 2 - 1 := by
    refine ⟨p - 1, ?_⟩
    rw [← hfactor]
    ring
  have h1mem : 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.one_mem_divisors.mpr (by omega)
  have h2mem : 2 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨h2dvd, by omega⟩
  have hpmmem : p - 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨hpm_dvd, by omega⟩
  have hppmem : p + 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨hpp_dvd, by omega⟩
  have hNmem : p ^ 2 - 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors_self _ (by omega)
  have hfive : 5 ≤ (p ^ 2 - 1).divisors.card := by
    apply five_le_card_of_chain_mem
      (a := 1) (b := 2) (c := p - 1) (d := p + 1) (e := p ^ 2 - 1)
    · norm_num
    · omega
    · omega
    · nlinarith
    · exact h1mem
    · exact h2mem
    · exact hpmmem
    · exact hppmem
    · exact hNmem
  rw [ArithmeticFunction.sigma_zero_apply]
  omega

@[category API, AMS 11]
private lemma two_mul_prime_of_even_sigma_zero_le_four {a : ℕ}
    (ha8 : 8 < a) (heven : 2 ∣ a) (htau : σ 0 a ≤ 4) :
    ∃ q : ℕ, q.Prime ∧ a = 2 * q := by
  set q := a / 2 with hq_def
  have haeq : 2 * q = a := by
    simpa [hq_def] using Nat.mul_div_cancel' heven
  have hq4 : 4 < q := by omega
  by_cases hqprime : q.Prime
  · exact ⟨q, hqprime, haeq.symm⟩
  · exfalso
    obtain ⟨r, hrprime, hrdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : q ≠ 1)
    have hrne : r ≠ q := by
      intro hrq
      exact hqprime (hrq ▸ hrprime)
    have hrle : r ≤ q := Nat.le_of_dvd (by omega) hrdvd
    have hrlt : r < q := lt_of_le_of_ne hrle hrne
    have ha0 : a ≠ 0 := by omega
    have h1mem : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha0
    have h2mem : 2 ∈ a.divisors := Nat.mem_divisors.mpr ⟨heven, ha0⟩
    have hamem : a ∈ a.divisors := Nat.mem_divisors_self a ha0
    have hq_dvd : q ∣ a := ⟨2, by rw [← haeq]; ring⟩
    have hqmem : q ∈ a.divisors := Nat.mem_divisors.mpr ⟨hq_dvd, ha0⟩
    have hcard : a.divisors.card ≤ 4 := by
      rwa [← ArithmeticFunction.sigma_zero_apply]
    by_cases hr2 : r = 2
    · subst r
      have h4dvd : 4 ∣ a := by
        obtain ⟨t, ht⟩ := hrdvd
        refine ⟨t, ?_⟩
        rw [← haeq, ht]
        ring
      have h4mem : 4 ∈ a.divisors := Nat.mem_divisors.mpr ⟨h4dvd, ha0⟩
      have hfive : 5 ≤ a.divisors.card := by
        apply five_le_card_of_chain_mem
          (a := 1) (b := 2) (c := 4) (d := q) (e := a)
        · norm_num
        · norm_num
        · exact hq4
        · omega
        · exact h1mem
        · exact h2mem
        · exact h4mem
        · exact hqmem
        · exact hamem
      omega
    · have h2r_dvd : 2 * r ∣ a := by
        obtain ⟨t, ht⟩ := hrdvd
        refine ⟨t, ?_⟩
        rw [← haeq, ht]
        ring
      have hr_dvd : r ∣ a := hrdvd.trans hq_dvd
      have hrmem : r ∈ a.divisors := Nat.mem_divisors.mpr ⟨hr_dvd, ha0⟩
      have h2rmem : 2 * r ∈ a.divisors := Nat.mem_divisors.mpr ⟨h2r_dvd, ha0⟩
      have hfive : 5 ≤ a.divisors.card := by
        apply five_le_card_of_chain_mem
          (a := 1) (b := 2) (c := r) (d := 2 * r) (e := a)
        · norm_num
        · exact lt_of_le_of_ne hrprime.two_le (Ne.symm hr2)
        · nlinarith [hrprime.two_le]
        · omega
        · exact h1mem
        · exact h2mem
        · exact hrmem
        · exact h2rmem
        · exact hamem
      omega

/-- Above the finite exceptional range, surviving shifts one and two is
exactly the Sophie Germain / safe-prime pattern. -/
@[category API, AMS 11]
theorem survives_depth_two_iff_sophie_germain {n : ℕ} (hn : 10 < n) :
    SurvivesThrough n 2 ↔
      ∃ q : ℕ, q.Prime ∧ (2 * q + 1).Prime ∧ n = 2 * q + 2 := by
  constructor
  · intro H
    have h1 : σ 0 (n - 1) ≤ 3 := by
      simpa [SurvivesThrough] using H 1 (by norm_num) (by norm_num) (by omega)
    have h2 : σ 0 (n - 2) ≤ 4 := by
      simpa [SurvivesThrough] using H 2 (by norm_num) (by norm_num) (by omega)
    obtain ⟨p, hp, hp_case | hp_case⟩ :=
      prime_or_prime_square_of_sigma_zero_le_three (a := n - 1) (by omega) h1
    · have hcop : Nat.Coprime 2 p := by
        rw [Nat.prime_two.coprime_iff_not_dvd]
        rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp]
        omega
      obtain ⟨t, ht⟩ := Nat.coprime_two_left.mp hcop
      have heven : 2 ∣ n - 2 := by
        refine ⟨t, ?_⟩
        omega
      obtain ⟨q, hq, hn2⟩ :=
        two_mul_prime_of_even_sigma_zero_le_four (a := n - 2)
          (by omega) heven h2
      refine ⟨q, hq, ?_, ?_⟩
      · convert hp using 1
        all_goals omega
      · omega
    · have hp5 : 5 ≤ p := by
        by_contra h
        have hp4 : p ≤ 4 := by omega
        interval_cases p
        · norm_num at hp
        · norm_num at hp
        · norm_num at hp_case
          omega
        · norm_num at hp_case
          omega
        · norm_num at hp
      have hbad := four_lt_sigma_zero_prime_square_sub_one hp hp5
      have hn2eq : n - 2 = p ^ 2 - 1 := by omega
      rw [hn2eq] at h2
      omega
  · rintro ⟨q, hq, hsafe, rfl⟩
    intro j hj0 hj2 hjn
    interval_cases j
    · have hsigma : σ 0 (2 * q + 1) = 2 := by
        simpa using
          (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hsafe)
      have hsub : 2 * q + 2 - 1 = 2 * q + 1 := by omega
      rw [hsub, hsigma]
      norm_num
    · by_cases hq2 : q = 2
      · subst q
        native_decide
      · have hcop : Nat.Coprime 2 q := by
          rw [Nat.prime_two.coprime_iff_not_dvd]
          rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq]
          exact Ne.symm hq2
        have hmul :=
          (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_mul_of_coprime hcop
        have hs2 : σ 0 2 = 2 := by
          simpa using
            (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) Nat.prime_two)
        have hsq : σ 0 q = 2 := by
          simpa using
            (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hq)
        rw [hs2, hsq] at hmul
        norm_num at hmul ⊢
        exact hmul.le

/-- The `k = 3` instance of the infinite-window variant is exactly the
classical infinitude problem for Sophie Germain primes.  Thus this theorem
identifies the first open window without claiming to solve it. -/
@[category API, AMS 11]
theorem infinite_window_three_iff_infinite_sophie_germain :
    {n | (⨆ m : Set.Ioo (n - 3) n,
      (m : ℕ) + σ 0 m) ≤ n + 2}.Infinite ↔
      {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Infinite := by
  have hset :
      {n | (⨆ m : Set.Ioo (n - 3) n,
        (m : ℕ) + σ 0 m) ≤ n + 2} =
      {n : ℕ | SurvivesThrough n 2} := by
    ext n
    simpa using (window_iff_shift_budgets n 3)
  rw [hset]
  constructor
  · intro hsurvivors
    by_contra hninf
    have hsafeFinite : {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Finite :=
      Set.not_infinite.mp hninf
    have himageFinite :
        ((fun q : ℕ ↦ 2 * q + 2) ''
          {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Finite :=
      hsafeFinite.image _
    have hsmallFinite : {n : ℕ | n ≤ 10}.Finite := Set.finite_le_nat 10
    have hunionFinite :
        ({n : ℕ | n ≤ 10} ∪
          (fun q : ℕ ↦ 2 * q + 2) ''
            {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Finite :=
      hsmallFinite.union himageFinite
    apply hsurvivors
    apply hunionFinite.subset
    intro n hn
    by_cases hn10 : n ≤ 10
    · exact Or.inl hn10
    · right
      obtain ⟨q, hq, hsafe, hnq⟩ :=
        (survives_depth_two_iff_sophie_germain (n := n) (by omega)).mp hn
      exact ⟨q, ⟨hq, hsafe⟩, hnq.symm⟩
  · intro hsafe
    have hwindow := infinite_window_three_of_infinite_sophie_germain hsafe
    rw [hset] at hwindow
    exact hwindow

/-- The limit variant is exactly the assertion that every sufficiently large
`n` has a failed shift whose excess is larger than any prescribed bound. -/
@[category API, AMS 11]
theorem lim_iff_eventual_shift_excess :
    atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop ↔
      ∀ B : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ k : ℕ, 0 < k ∧ k < n ∧ B + k < σ 0 (n - k) := by
  constructor
  · intro hlim B
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hlim (B + 1)
    refine ⟨max N 2, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hB : B + 1 ≤ ⨆ m : Fin n, σ 0 m + m - n := hN n hnN
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    obtain ⟨m, hm⟩ :
        ∃ m : Fin n, σ 0 m + m - n = ⨆ i : Fin n, σ 0 i + i - n :=
      exists_eq_ciSup_of_finite
    have hBm : B + 1 ≤ σ 0 m + (m : ℕ) - n := by
      rw [hm]
      exact hB
    have hm0 : (m : ℕ) ≠ 0 := by
      intro hmzero
      have hs0 : σ 0 (0 : ℕ) = 0 := by native_decide
      rw [hmzero, hs0] at hBm
      omega
    let k := n - (m : ℕ)
    refine ⟨k, ?_, ?_, ?_⟩
    · dsimp [k]
      omega
    · dsimp [k]
      omega
    · dsimp [k]
      have hm_lt : (m : ℕ) < n := m.isLt
      have hnkm : n - (n - (m : ℕ)) = (m : ℕ) := by omega
      rw [hnkm]
      omega
  · intro hshift
    rw [tendsto_atTop_atTop]
    intro B
    obtain ⟨N, hN⟩ := hshift B
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    obtain ⟨k, hk0, hkn, hkfail⟩ := hN n hnN
    let m : Fin n := ⟨n - k, by omega⟩
    have hterm : B ≤ σ 0 m + (m : ℕ) - n := by
      dsimp [m]
      omega
    have hbdd : BddAbove (Set.range fun i : Fin n ↦ σ 0 i + (i : ℕ) - n) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨i, rfl⟩
      dsimp
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (i : ℕ)
      have hi : (i : ℕ) < n := i.isLt
      omega
    exact hterm.trans (le_ciSup hbdd m)

/-- Prime powers show that the sequence in the limit variant is unbounded
along an explicit subsequence.  This is weaker than convergence to `atTop`. -/
@[category API, AMS 11]
theorem prime_power_subsequence_lower_bound (B : ℕ) :
    B ≤ ⨆ m : Fin (2 ^ B + 1), σ 0 m + m - (2 ^ B + 1) := by
  let m : Fin (2 ^ B + 1) := ⟨2 ^ B, by omega⟩
  have hterm : B ≤ σ 0 m + (m : ℕ) - (2 ^ B + 1) := by
    dsimp [m]
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]
    omega
  have hbdd :
      BddAbove
        (Set.range fun i : Fin (2 ^ B + 1) ↦
          σ 0 i + (i : ℕ) - (2 ^ B + 1)) := by
    refine ⟨2 * (2 ^ B + 1), ?_⟩
    rintro y ⟨i, rfl⟩
    dsimp
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (i : ℕ)
    have hi : (i : ℕ) < 2 ^ B + 1 := i.isLt
    omega
  exact hterm.trans (le_ciSup hbdd m)

/-- The limit sequence is unbounded, although its conjectured convergence to
`atTop` remains open. -/
@[category API, AMS 11]
theorem lim_sequence_unbounded :
    ∀ B : ℕ, ∃ n : ℕ,
      B ≤ ⨆ m : Fin n, σ 0 m + m - n := by
  intro B
  exact ⟨2 ^ B + 1, prime_power_subsequence_lower_bound B⟩

/-- The conjectured limit would force all sufficiently large integers to fail
the original candidate condition. -/
@[category API, AMS 11]
theorem lim_implies_eventually_not_candidate
    (hlim : atTop.Tendsto
      (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop) :
    ∀ᶠ n : ℕ in atTop, ¬Candidate n := by
  have hlarge := tendsto_atTop.mp hlim 3
  filter_upwards [hlarge] with n hn
  intro hcand
  have hexcess := (candidate_iff_excess_le_two n).mp hcand |>.2
  omega

/-- Consequently, the conjectured limit would make the set of candidates
finite. -/
@[category API, AMS 11]
theorem lim_implies_finite_candidates
    (hlim : atTop.Tendsto
      (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop) :
    {n : ℕ | Candidate n}.Finite := by
  classical
  have h := lim_implies_eventually_not_candidate hlim
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h
  simpa only [not_not] using h

/-- Let $\tau(n)$ count the number of divisors of $n$. Is there some $n > 24$ such that
$$
  \max_{m < n}(m + \tau(m)) \leq n + 2?
$$ -/
@[category research open, AMS 11]
theorem erdos_647 : answer(sorry) ↔ ∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2 := by
  sorry

/-- This is true for $n = 24$. -/
@[category research solved, AMS 11]
theorem erdos_647.variants.twenty_four : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

/-- Erdős says 'it is extremely doubtful' that there are infinitely many such $n$, and in
fact suggests that
$$
  lim_{n\to\infty} \max_{m < n}(\tau(m) + m − n) = \infty.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.lim :
    answer(sorry) ↔ atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop := by
  sorry

/-- Erdős says it 'seems certain' that for every $k$ there are infinitely many $n$
for which
$$
  \max_{n−k < m < n}(m + \tau(m)) ≤ n + 2.
$$ -/
@[category research open, AMS 11]
theorem erdos_647.variants.infinite :
    answer(sorry) ↔ ∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite := by
  sorry

end Erdos647
