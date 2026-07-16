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
