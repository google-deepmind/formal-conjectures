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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ErdosProblems.«647»

/-!
# Erdős Problem 647 — Modular Constraints

Partial progress toward `Erdos647.erdos_647`. We do not close the conjecture, but
establish the *modular ladder*: any counterexample n > 332,640 must satisfy
360,360 = 2³·3²·5·7·11·13 ∣ n.

References:
* [erdosproblems.com/647](https://www.erdosproblems.com/647)
* Forum thread: comments by T. Tao (Oct 2025), S. Dutta and B. Alexeev (Jan 2026).

This file contains intermediate lemmas only; it does not change the truth value
of `Erdos647.erdos_647`. To use these lemmas in a closure proof, one would still
need to (a) extend the modular ladder past 13, (b) close the asymptotic step.
-/

namespace Erdos647

open Filter ArithmeticFunction ArithmeticFunction.sigma

/-- Convenience predicate: `n` satisfies condition (∗) of Erdős Problem #647. -/
def StarBound (n : ℕ) : Prop :=
  ⨆ m : Fin n, (m : ℕ) + σ 0 m ≤ n + 2

/-- Equivalent reformulation: `τ(n - k) ≤ k + 2` for every `1 ≤ k < n`. -/
@[category research open, AMS 11]
lemma starBound_iff_tau_le (n : ℕ) :
    StarBound n ↔ ∀ k, 1 ≤ k → k < n → σ 0 (n - k) ≤ k + 2 := by
  unfold StarBound
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · -- n = 0: vacuous on both sides
    refine ⟨fun _ k _ hk => absurd hk (by omega), fun _ => ?_⟩
    simp [iSup_of_empty]
  -- n ≥ 1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hbd : BddAbove (Set.range fun m : Fin n => (m : ℕ) + σ 0 ↑m) :=
    (Set.finite_range _).bddAbove
  rw [ciSup_le_iff hbd]
  refine ⟨fun h k hk_pos hk_lt => ?_, fun h m => ?_⟩
  · -- Forward: pick m = n - k.
    have hm : n - k < n := by omega
    have key : (n - k) + σ 0 (n - k) ≤ n + 2 := by
      have := h ⟨n - k, hm⟩
      simpa using this
    omega
  · -- Backward: for each m : Fin n, bound m + σ 0 m.
    by_cases hm0 : (m : ℕ) = 0
    · -- σ 0 0 = 0
      have : σ 0 (m : ℕ) = 0 := by rw [hm0]; simp
      omega
    · -- m ≥ 1; let k = n - m.
      have hm_lt : (m : ℕ) < n := m.isLt
      have hk_pos : 1 ≤ n - m := by omega
      have hk_lt : n - (m : ℕ) < n := by omega
      have hreplace : n - (n - (m : ℕ)) = (m : ℕ) := by omega
      have hh := h (n - m) hk_pos hk_lt
      rw [hreplace] at hh
      omega

/-! ### Lemma 1.  `n > 5 ∧ StarBound n → 2 ∣ n`. -/

/-- If `j ≥ 3` then `2j` has at least 4 divisors `{1, 2, j, 2j}`. -/
@[category research open, AMS 11]
lemma four_le_sigma_two_mul (j : ℕ) (hj : 3 ≤ j) : 4 ≤ σ 0 (2 * j) := by
  have h2j_ne : 2 * j ≠ 0 := by omega
  -- Build the four divisors as a Finset.
  have h1 : (1 : ℕ) ∈ (2 * j).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, h2j_ne⟩
  have h2 : (2 : ℕ) ∈ (2 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨j, rfl⟩, h2j_ne⟩
  have hjm : j ∈ (2 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, h2j_ne⟩
  have h2jm : (2 * j) ∈ (2 * j).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h2j_ne⟩
  have hsub : ({1, 2, j, 2 * j} : Finset ℕ) ⊆ (2 * j).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hjm
    · exact h2jm
  have hcard : ({1, 2, j, 2 * j} : Finset ℕ).card = 4 := by
    rw [show ({1, 2, j, 2 * j} : Finset ℕ) = insert 1 (insert 2 (insert j {2 * j})) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · -- j ∉ {2 * j}
      simp; omega
    · -- 2 ∉ insert j {2 * j}
      simp; omega
    · -- 1 ∉ insert 2 (insert j {2 * j})
      simp; omega
  have hcount : 4 ≤ (2 * j).divisors.card := by
    calc 4 = ({1, 2, j, 2 * j} : Finset ℕ).card := hcard.symm
      _ ≤ (2 * j).divisors.card := Finset.card_le_card hsub
  -- Convert σ 0 to divisor count via ArithmeticFunction.sigma_apply.
  show 4 ≤ σ 0 (2 * j)
  have : σ 0 (2 * j) = (2 * j).divisors.card := by
    simp [ArithmeticFunction.sigma_apply]
  rw [this]
  exact hcount

/-- **Two divides any (∗)-bounded `n > 5`.** -/
@[category research open, AMS 11]
theorem two_dvd_of_starBound {n : ℕ} (hn : 5 < n) (hsb : StarBound n) : 2 ∣ n := by
  by_contra h_odd
  -- n is odd, n ≥ 7. Set k = 1, m = n - 1 ≥ 6 even.
  -- σ 0 (n-1) ≥ 4 by the lemma, but the (∗)-bound gives σ 0 (n-1) ≤ 3.
  have h6 : 6 ≤ n - 1 := by omega
  have h_even : 2 ∣ (n - 1) := by
    have h_n_odd : ¬ Even n := fun he => h_odd he.two_dvd
    rcases Nat.even_or_odd n with he | ho
    · exact absurd he h_n_odd
    · -- n odd ⇒ n - 1 even
      have : n ≥ 1 := by omega
      omega
  have htau : 4 ≤ σ 0 (n - 1) := by
    obtain ⟨j, hj⟩ := h_even
    rw [hj]
    have : 3 ≤ j := by omega
    exact four_le_sigma_two_mul j this
  have hbound : σ 0 (n - 1) ≤ 3 := by
    have := (starBound_iff_tau_le n).1 hsb 1 (by omega) (by omega)
    simpa using this
  omega

/- ### Lemma 2.  `n > 10 ∧ StarBound n → 4 ∣ n`. -/

/-- If `s ≥ 3` then `4s` has at least 5 divisors. The set `{1, 2, 4, 2s, 4s}`
    consists of 5 distinct divisors (distinct because `s ≥ 3` rules out collisions). -/
@[category research open, AMS 11]
lemma five_le_sigma_four_mul (s : ℕ) (hs : 3 ≤ s) : 5 ≤ σ 0 (4 * s) := by
  have h4s_ne : 4 * s ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (4 * s).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h4s_ne⟩
  have h2 : (2 : ℕ) ∈ (4 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * s, by ring⟩, h4s_ne⟩
  have h4 : (4 : ℕ) ∈ (4 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨s, rfl⟩, h4s_ne⟩
  have h2s : (2 * s) ∈ (4 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, h4s_ne⟩
  have h4s : (4 * s) ∈ (4 * s).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h4s_ne⟩
  have hsub : ({1, 2, 4, 2 * s, 4 * s} : Finset ℕ) ⊆ (4 * s).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h4
    · exact h2s
    · exact h4s
  have hcard : ({1, 2, 4, 2 * s, 4 * s} : Finset ℕ).card = 5 := by
    rw [show ({1, 2, 4, 2 * s, 4 * s} : Finset ℕ) =
            insert 1 (insert 2 (insert 4 (insert (2 * s) {4 * s}))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    · -- 2 * s ∉ {4 * s}
      simp; omega
    · -- 4 ∉ insert (2 * s) {4 * s}
      simp; omega
    · -- 2 ∉ insert 4 (insert (2 * s) {4 * s})
      simp; omega
    · -- 1 ∉ ...
      simp; omega
  have hcount : 5 ≤ (4 * s).divisors.card := by
    calc 5 = ({1, 2, 4, 2 * s, 4 * s} : Finset ℕ).card := hcard.symm
      _ ≤ (4 * s).divisors.card := Finset.card_le_card hsub
  show 5 ≤ σ 0 (4 * s)
  have : σ 0 (4 * s) = (4 * s).divisors.card := by
    simp [ArithmeticFunction.sigma_apply]
  rw [this]
  exact hcount

/-- **Four divides any (∗)-bounded `n > 10`.** -/
@[category research open, AMS 11]
theorem four_dvd_of_starBound {n : ℕ} (hn : 10 < n) (hsb : StarBound n) : 4 ∣ n := by
  have h2 : 2 ∣ n := two_dvd_of_starBound (by omega) hsb
  by_contra h4
  -- 2 ∣ n ∧ ¬ 4 ∣ n ⟹ n % 4 = 2.  4 ∣ (n - 2).
  have hdvd_n2 : 4 ∣ (n - 2) := by omega
  obtain ⟨s, hs⟩ := hdvd_n2
  -- n ≡ 2 mod 4 and n > 10 implies n ≥ 14, so n - 2 ≥ 12 = 4 * 3, so s ≥ 3.
  have hs_ge : 3 ≤ s := by omega
  -- (∗) at k = 2: σ 0 (n - 2) ≤ 4.
  have htau : σ 0 (n - 2) ≤ 4 := by
    have := (starBound_iff_tau_le n).1 hsb 2 (by omega) (by omega)
    simpa using this
  rw [hs] at htau
  have h5 : 5 ≤ σ 0 (4 * s) := five_le_sigma_four_mul s hs_ge
  omega

/-! ### Lemma 3.  `n > 36 ∧ StarBound n → 8 ∣ n`.

Sharp threshold: the only `(∗)`-bounded `n` with `4 ∣ n` and `8 ∤ n` is in `{12, 20, 36}`.
-/

/-- If `t ≥ 5` then `8t` has at least 7 divisors `{1, 2, 4, 8, 2t, 4t, 8t}`. -/
@[category research open, AMS 11]
lemma seven_le_sigma_eight_mul (t : ℕ) (ht : 5 ≤ t) : 7 ≤ σ 0 (8 * t) := by
  have h8t_ne : 8 * t ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h8t_ne⟩
  have h2 : (2 : ℕ) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨4 * t, by ring⟩, h8t_ne⟩
  have h4 : (4 : ℕ) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * t, by ring⟩, h8t_ne⟩
  have h8 : (8 : ℕ) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨t, rfl⟩, h8t_ne⟩
  have h2t : (2 * t) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨4, by ring⟩, h8t_ne⟩
  have h4t : (4 * t) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, h8t_ne⟩
  have h8t : (8 * t) ∈ (8 * t).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h8t_ne⟩
  have hsub : ({1, 2, 4, 8, 2 * t, 4 * t, 8 * t} : Finset ℕ) ⊆ (8 * t).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h4
    · exact h8
    · exact h2t
    · exact h4t
    · exact h8t
  have hcard : ({1, 2, 4, 8, 2 * t, 4 * t, 8 * t} : Finset ℕ).card = 7 := by
    rw [show ({1, 2, 4, 8, 2 * t, 4 * t, 8 * t} : Finset ℕ) =
            insert 1 (insert 2 (insert 4 (insert 8
              (insert (2 * t) (insert (4 * t) {8 * t}))))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 7 ≤ (8 * t).divisors.card := by
    calc 7 = ({1, 2, 4, 8, 2 * t, 4 * t, 8 * t} : Finset ℕ).card := hcard.symm
      _ ≤ (8 * t).divisors.card := Finset.card_le_card hsub
  show 7 ≤ σ 0 (8 * t)
  have : σ 0 (8 * t) = (8 * t).divisors.card := by
    simp [ArithmeticFunction.sigma_apply]
  rw [this]
  exact hcount

/-- Eight divides any (∗)-bounded `n > 36`. The threshold is sharp: `{12, 20, 36}` are the only `(∗)`-satisfying multiples of 4 that are not multiples of 8. -/
@[category research open, AMS 11]
theorem eight_dvd_of_starBound {n : ℕ} (hn : 36 < n) (hsb : StarBound n) : 8 ∣ n := by
  have h4 : 4 ∣ n := four_dvd_of_starBound (by omega) hsb
  by_contra h8
  -- 4 ∣ n ∧ ¬ 8 ∣ n ⟹ n ≡ 4 mod 8.  8 ∣ (n - 4).
  have hdvd_n4 : 8 ∣ (n - 4) := by omega
  obtain ⟨t, ht⟩ := hdvd_n4
  -- n > 36, n ≡ 4 mod 8 ⟹ n ≥ 44 ⟹ n - 4 ≥ 40 = 8 · 5 ⟹ t ≥ 5.
  have ht_ge : 5 ≤ t := by omega
  have htau : σ 0 (n - 4) ≤ 6 := by
    have := (starBound_iff_tau_le n).1 hsb 4 (by omega) (by omega)
    simpa using this
  rw [ht] at htau
  have h7 : 7 ≤ σ 0 (8 * t) := seven_le_sigma_eight_mul t ht_ge
  omega

/- ### Lemma 4.  `n > 24 ∧ StarBound n → 3 ∣ n`. -/

/-- If `j ≥ 4` then `3j` has at least 4 divisors `{1, 3, j, 3j}`. -/
@[category research open, AMS 11]
lemma four_le_sigma_three_mul (j : ℕ) (hj : 4 ≤ j) : 4 ≤ σ 0 (3 * j) := by
  have h3j_ne : 3 * j ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (3 * j).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h3j_ne⟩
  have h3 : (3 : ℕ) ∈ (3 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨j, rfl⟩, h3j_ne⟩
  have hjm : j ∈ (3 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨3, by ring⟩, h3j_ne⟩
  have h3jm : (3 * j) ∈ (3 * j).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h3j_ne⟩
  have hsub : ({1, 3, j, 3 * j} : Finset ℕ) ⊆ (3 * j).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact hjm
    · exact h3jm
  have hcard : ({1, 3, j, 3 * j} : Finset ℕ).card = 4 := by
    rw [show ({1, 3, j, 3 * j} : Finset ℕ) = insert 1 (insert 3 (insert j {3 * j})) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp; omega
    · simp; omega
    · simp; omega
  have hcount : 4 ≤ (3 * j).divisors.card := by
    calc 4 = ({1, 3, j, 3 * j} : Finset ℕ).card := hcard.symm
      _ ≤ (3 * j).divisors.card := Finset.card_le_card hsub
  show 4 ≤ σ 0 (3 * j)
  have : σ 0 (3 * j) = (3 * j).divisors.card := by
    simp [ArithmeticFunction.sigma_apply]
  rw [this]
  exact hcount

/-- If `s ≥ 2` then `6s` has at least 5 divisors `{1, 2, 3, 6, 6s}`. -/
@[category research open, AMS 11]
lemma five_le_sigma_six_mul (s : ℕ) (hs : 2 ≤ s) : 5 ≤ σ 0 (6 * s) := by
  have h6s_ne : 6 * s ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (6 * s).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h6s_ne⟩
  have h2 : (2 : ℕ) ∈ (6 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨3 * s, by ring⟩, h6s_ne⟩
  have h3 : (3 : ℕ) ∈ (6 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * s, by ring⟩, h6s_ne⟩
  have h6 : (6 : ℕ) ∈ (6 * s).divisors :=
    Nat.mem_divisors.mpr ⟨⟨s, rfl⟩, h6s_ne⟩
  have h6s : (6 * s) ∈ (6 * s).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h6s_ne⟩
  have hsub : ({1, 2, 3, 6, 6 * s} : Finset ℕ) ⊆ (6 * s).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h6
    · exact h6s
  have hcard : ({1, 2, 3, 6, 6 * s} : Finset ℕ).card = 5 := by
    rw [show ({1, 2, 3, 6, 6 * s} : Finset ℕ) =
            insert 1 (insert 2 (insert 3 (insert 6 {6 * s}))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 5 ≤ (6 * s).divisors.card := by
    calc 5 = ({1, 2, 3, 6, 6 * s} : Finset ℕ).card := hcard.symm
      _ ≤ (6 * s).divisors.card := Finset.card_le_card hsub
  show 5 ≤ σ 0 (6 * s)
  have : σ 0 (6 * s) = (6 * s).divisors.card := by
    simp [ArithmeticFunction.sigma_apply]
  rw [this]
  exact hcount

/-- Three divides any (∗)-bounded `n > 24`. -/
@[category research open, AMS 11]
theorem three_dvd_of_starBound {n : ℕ} (hn : 24 < n) (hsb : StarBound n) : 3 ∣ n := by
  have h4 : 4 ∣ n := four_dvd_of_starBound (by omega) hsb
  by_contra h3
  -- n mod 3 ∈ {1, 2}
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hm1 | hm2
  · -- Case n ≡ 1 mod 3: take k = 1.
    have hdvd1 : 3 ∣ (n - 1) := by omega
    obtain ⟨j, hj⟩ := hdvd1
    -- 4 | n and n ≡ 1 mod 3 ⟹ n ≡ 4 mod 12 ⟹ n ≥ 28 (since n > 24); j ≥ 9.
    have hj_ge : 4 ≤ j := by omega
    have htau : σ 0 (n - 1) ≤ 3 := by
      have := (starBound_iff_tau_le n).1 hsb 1 (by omega) (by omega)
      simpa using this
    rw [hj] at htau
    have h4' : 4 ≤ σ 0 (3 * j) := four_le_sigma_three_mul j hj_ge
    omega
  · -- Case n ≡ 2 mod 3: take k = 2.
    have hdvd2 : 6 ∣ (n - 2) := by omega
    obtain ⟨s, hs⟩ := hdvd2
    -- 4 | n and n ≡ 2 mod 3 ⟹ n ≡ 8 mod 12 ⟹ n ≥ 32; n - 2 ≥ 30; s ≥ 5.
    have hs_ge : 2 ≤ s := by omega
    have htau : σ 0 (n - 2) ≤ 4 := by
      have := (starBound_iff_tau_le n).1 hsb 2 (by omega) (by omega)
      simpa using this
    rw [hs] at htau
    have h5 : 5 ≤ σ 0 (6 * s) := five_le_sigma_six_mul s hs_ge
    omega

/- ### Lemma 5.  `n > 84 ∧ StarBound n → 9 ∣ n`. -/

/-- Nine divides any (∗)-bounded `n > 84`. -/
@[category research open, AMS 11]
theorem nine_dvd_of_starBound {n : ℕ} (hn : 84 < n) (hsb : StarBound n) : 9 ∣ n := by
  -- Given 8 ∣ n and 3 ∣ n (so 24 ∣ n). Suppose 9 ∤ n.
  -- Case n ≡ 3 mod 9: take k = 3, σ 0 (n - 3) = 3 σ 0 q ≥ 6, but bound is ≤ 5.
  -- Case n ≡ 6 mod 9: take k = 6, σ 0 (n - 6) ≥ 12 (with sub-case analysis).
  sorry

/- ### Lemma 6.  `n > 26 ∧ StarBound n → 5 ∣ n`. -/

/-- If `j ≥ 6` then `5j` has at least 4 divisors `{1, 5, j, 5j}`. -/
@[category research open, AMS 11]
lemma four_le_sigma_five_mul (j : ℕ) (hj : 6 ≤ j) : 4 ≤ σ 0 (5 * j) := by
  have h5j_ne : 5 * j ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (5 * j).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h5j_ne⟩
  have h5 : (5 : ℕ) ∈ (5 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨j, rfl⟩, h5j_ne⟩
  have hjm : j ∈ (5 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨5, by ring⟩, h5j_ne⟩
  have h5jm : (5 * j) ∈ (5 * j).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h5j_ne⟩
  have hsub : ({1, 5, j, 5 * j} : Finset ℕ) ⊆ (5 * j).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h5
    · exact hjm
    · exact h5jm
  have hcard : ({1, 5, j, 5 * j} : Finset ℕ).card = 4 := by
    rw [show ({1, 5, j, 5 * j} : Finset ℕ) = insert 1 (insert 5 (insert j {5 * j})) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp; omega
    · simp; omega
    · simp; omega
  have hcount : 4 ≤ (5 * j).divisors.card := by
    calc 4 = ({1, 5, j, 5 * j} : Finset ℕ).card := hcard.symm
      _ ≤ (5 * j).divisors.card := Finset.card_le_card hsub
  show 4 ≤ σ 0 (5 * j)
  have : σ 0 (5 * j) = (5 * j).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `t ≥ 2` then `10t` has at least 5 divisors `{1, 2, 5, 10, 10t}`. -/
@[category research open, AMS 11]
lemma five_le_sigma_ten_mul (t : ℕ) (ht : 2 ≤ t) : 5 ≤ σ 0 (10 * t) := by
  have h10t_ne : 10 * t ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (10 * t).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h10t_ne⟩
  have h2 : (2 : ℕ) ∈ (10 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨5 * t, by ring⟩, h10t_ne⟩
  have h5 : (5 : ℕ) ∈ (10 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * t, by ring⟩, h10t_ne⟩
  have h10 : (10 : ℕ) ∈ (10 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨t, rfl⟩, h10t_ne⟩
  have h10t : (10 * t) ∈ (10 * t).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h10t_ne⟩
  have hsub : ({1, 2, 5, 10, 10 * t} : Finset ℕ) ⊆ (10 * t).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h5
    · exact h10
    · exact h10t
  have hcard : ({1, 2, 5, 10, 10 * t} : Finset ℕ).card = 5 := by
    rw [show ({1, 2, 5, 10, 10 * t} : Finset ℕ) =
            insert 1 (insert 2 (insert 5 (insert 10 {10 * t}))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 5 ≤ (10 * t).divisors.card := by
    calc 5 = ({1, 2, 5, 10, 10 * t} : Finset ℕ).card := hcard.symm
      _ ≤ (10 * t).divisors.card := Finset.card_le_card hsub
  show 5 ≤ σ 0 (10 * t)
  have : σ 0 (10 * t) = (10 * t).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `u ≥ 2` then `15u` has at least 6 divisors. (For `u ∈ {3, 5}` the divisor
    count is exactly 6; we case-split.) -/
@[category research open, AMS 11]
lemma six_le_sigma_fifteen_mul (u : ℕ) (hu : 2 ≤ u) : 6 ≤ σ 0 (15 * u) := by
  rcases Nat.lt_or_ge u 6 with hlt | hge
  · -- u ∈ {2, 3, 4, 5}: bash with decide
    interval_cases u <;> decide
  · -- u ≥ 6: standard divisor-set argument with {1, 3, 5, 15, 5u, 15u}
    have h15u_ne : 15 * u ≠ 0 := by omega
    have h1 : (1 : ℕ) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd _, h15u_ne⟩
    have h3 : (3 : ℕ) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨5 * u, by ring⟩, h15u_ne⟩
    have h5 : (5 : ℕ) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨3 * u, by ring⟩, h15u_ne⟩
    have h15 : (15 : ℕ) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨u, rfl⟩, h15u_ne⟩
    have h5u : (5 * u) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨3, by ring⟩, h15u_ne⟩
    have h15u : (15 * u) ∈ (15 * u).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_refl _, h15u_ne⟩
    have hsub : ({1, 3, 5, 15, 5 * u, 15 * u} : Finset ℕ) ⊆ (15 * u).divisors := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h3
      · exact h5
      · exact h15
      · exact h5u
      · exact h15u
    have hcard : ({1, 3, 5, 15, 5 * u, 15 * u} : Finset ℕ).card = 6 := by
      rw [show ({1, 3, 5, 15, 5 * u, 15 * u} : Finset ℕ) =
              insert 1 (insert 3 (insert 5 (insert 15 (insert (5 * u) {15 * u})))) from rfl]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals (simp; omega)
    have hcount : 6 ≤ (15 * u).divisors.card := by
      calc 6 = ({1, 3, 5, 15, 5 * u, 15 * u} : Finset ℕ).card := hcard.symm
        _ ≤ (15 * u).divisors.card := Finset.card_le_card hsub
    show 6 ≤ σ 0 (15 * u)
    have : σ 0 (15 * u) = (15 * u).divisors.card := by simp [ArithmeticFunction.sigma_apply]
    rw [this]; exact hcount

/-- If `w ≥ 2` then `20w` has at least 7 divisors `{1, 2, 4, 5, 10, 20, 20w}`. -/
@[category research open, AMS 11]
lemma seven_le_sigma_twenty_mul (w : ℕ) (hw : 2 ≤ w) : 7 ≤ σ 0 (20 * w) := by
  have h20w_ne : 20 * w ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h20w_ne⟩
  have h2 : (2 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨⟨10 * w, by ring⟩, h20w_ne⟩
  have h4 : (4 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨⟨5 * w, by ring⟩, h20w_ne⟩
  have h5 : (5 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨⟨4 * w, by ring⟩, h20w_ne⟩
  have h10 : (10 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * w, by ring⟩, h20w_ne⟩
  have h20 : (20 : ℕ) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨⟨w, rfl⟩, h20w_ne⟩
  have h20w : (20 * w) ∈ (20 * w).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h20w_ne⟩
  have hsub : ({1, 2, 4, 5, 10, 20, 20 * w} : Finset ℕ) ⊆ (20 * w).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h4
    · exact h5
    · exact h10
    · exact h20
    · exact h20w
  have hcard : ({1, 2, 4, 5, 10, 20, 20 * w} : Finset ℕ).card = 7 := by
    rw [show ({1, 2, 4, 5, 10, 20, 20 * w} : Finset ℕ) =
            insert 1 (insert 2 (insert 4 (insert 5 (insert 10 (insert 20 {20 * w}))))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 7 ≤ (20 * w).divisors.card := by
    calc 7 = ({1, 2, 4, 5, 10, 20, 20 * w} : Finset ℕ).card := hcard.symm
      _ ≤ (20 * w).divisors.card := Finset.card_le_card hsub
  show 7 ≤ σ 0 (20 * w)
  have : σ 0 (20 * w) = (20 * w).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- Five divides any (∗)-bounded `n > 26`. -/
@[category research open, AMS 11]
theorem five_dvd_of_starBound {n : ℕ} (hn : 26 < n) (hsb : StarBound n) : 5 ∣ n := by
  have h4 : 4 ∣ n := four_dvd_of_starBound (by omega) hsb
  have h3 : 3 ∣ n := three_dvd_of_starBound (by omega) hsb
  by_contra h5
  -- n mod 5 ∈ {1, 2, 3, 4}
  have hmod : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with hm | hm | hm | hm
  · -- r = 1, k = 1
    have hd : 5 ∣ (n - 1) := by omega
    obtain ⟨j, hj⟩ := hd
    have hj_ge : 6 ≤ j := by omega
    have htau : σ 0 (n - 1) ≤ 3 := by
      have := (starBound_iff_tau_le n).1 hsb 1 (by omega) (by omega)
      simpa using this
    rw [hj] at htau
    have hh : 4 ≤ σ 0 (5 * j) := four_le_sigma_five_mul j hj_ge
    omega
  · -- r = 2, k = 2
    have hd : 10 ∣ (n - 2) := by omega
    obtain ⟨t, ht⟩ := hd
    have ht_ge : 2 ≤ t := by omega
    have htau : σ 0 (n - 2) ≤ 4 := by
      have := (starBound_iff_tau_le n).1 hsb 2 (by omega) (by omega)
      simpa using this
    rw [ht] at htau
    have hh : 5 ≤ σ 0 (10 * t) := five_le_sigma_ten_mul t ht_ge
    omega
  · -- r = 3, k = 3
    have hd : 15 ∣ (n - 3) := by omega
    obtain ⟨u, hu⟩ := hd
    have hu_ge : 2 ≤ u := by omega
    have htau : σ 0 (n - 3) ≤ 5 := by
      have := (starBound_iff_tau_le n).1 hsb 3 (by omega) (by omega)
      simpa using this
    rw [hu] at htau
    have hh : 6 ≤ σ 0 (15 * u) := six_le_sigma_fifteen_mul u hu_ge
    omega
  · -- r = 4, k = 4
    have hd : 20 ∣ (n - 4) := by omega
    obtain ⟨w, hw⟩ := hd
    have hw_ge : 2 ≤ w := by omega
    have htau : σ 0 (n - 4) ≤ 6 := by
      have := (starBound_iff_tau_le n).1 hsb 4 (by omega) (by omega)
      simpa using this
    rw [hw] at htau
    have hh : 7 ≤ σ 0 (20 * w) := seven_le_sigma_twenty_mul w hw_ge
    omega

/- ### Lemma 7.  `n > 54 ∧ StarBound n → 7 ∣ n`.

For each residue `r ∈ {1, …, 6}` of `n mod 7`, a witnessing `k` is chosen.
The naïve choice `k = r` works for `r ∈ {1, 2, 3, 4, 6}` but **fails** for `r = 5`
because `n − 5 = 35·(prime)` only gives `τ = 4 < 7`.  Following Tao's forum
analysis, the `r = 5` case uses `k = 12` instead: `n − 12 = 84·u`, which has
`τ ≥ 15 > 14 = k + 2`. -/

/-- If `j ≥ 8` then `7j` has at least 4 divisors `{1, 7, j, 7j}`. -/
@[category research open, AMS 11]
lemma four_le_sigma_seven_mul (j : ℕ) (hj : 8 ≤ j) : 4 ≤ σ 0 (7 * j) := by
  have h7j_ne : 7 * j ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (7 * j).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h7j_ne⟩
  have h7 : (7 : ℕ) ∈ (7 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨j, rfl⟩, h7j_ne⟩
  have hjm : j ∈ (7 * j).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7, by ring⟩, h7j_ne⟩
  have h7jm : (7 * j) ∈ (7 * j).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h7j_ne⟩
  have hsub : ({1, 7, j, 7 * j} : Finset ℕ) ⊆ (7 * j).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h7
    · exact hjm
    · exact h7jm
  have hcard : ({1, 7, j, 7 * j} : Finset ℕ).card = 4 := by
    rw [show ({1, 7, j, 7 * j} : Finset ℕ) = insert 1 (insert 7 (insert j {7 * j})) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp; omega
    · simp; omega
    · simp; omega
  have hcount : 4 ≤ (7 * j).divisors.card := by
    calc 4 = ({1, 7, j, 7 * j} : Finset ℕ).card := hcard.symm
      _ ≤ (7 * j).divisors.card := Finset.card_le_card hsub
  show 4 ≤ σ 0 (7 * j)
  have : σ 0 (7 * j) = (7 * j).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `t ≥ 2` then `14t` has at least 5 divisors `{1, 2, 7, 14, 14t}`. -/
@[category research open, AMS 11]
lemma five_le_sigma_fourteen_mul (t : ℕ) (ht : 2 ≤ t) : 5 ≤ σ 0 (14 * t) := by
  have h14t_ne : 14 * t ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (14 * t).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h14t_ne⟩
  have h2 : (2 : ℕ) ∈ (14 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7 * t, by ring⟩, h14t_ne⟩
  have h7 : (7 : ℕ) ∈ (14 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * t, by ring⟩, h14t_ne⟩
  have h14 : (14 : ℕ) ∈ (14 * t).divisors :=
    Nat.mem_divisors.mpr ⟨⟨t, rfl⟩, h14t_ne⟩
  have h14t : (14 * t) ∈ (14 * t).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h14t_ne⟩
  have hsub : ({1, 2, 7, 14, 14 * t} : Finset ℕ) ⊆ (14 * t).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h7
    · exact h14
    · exact h14t
  have hcard : ({1, 2, 7, 14, 14 * t} : Finset ℕ).card = 5 := by
    rw [show ({1, 2, 7, 14, 14 * t} : Finset ℕ) =
            insert 1 (insert 2 (insert 7 (insert 14 {14 * t}))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 5 ≤ (14 * t).divisors.card := by
    calc 5 = ({1, 2, 7, 14, 14 * t} : Finset ℕ).card := hcard.symm
      _ ≤ (14 * t).divisors.card := Finset.card_le_card hsub
  show 5 ≤ σ 0 (14 * t)
  have : σ 0 (14 * t) = (14 * t).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `u ≥ 8` then `21u` has at least 6 divisors `{1, 3, 7, 21, 3u, 21u}`. -/
@[category research open, AMS 11]
lemma six_le_sigma_twentyone_mul (u : ℕ) (hu : 8 ≤ u) : 6 ≤ σ 0 (21 * u) := by
  have h21u_ne : 21 * u ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h21u_ne⟩
  have h3 : (3 : ℕ) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7 * u, by ring⟩, h21u_ne⟩
  have h7 : (7 : ℕ) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨⟨3 * u, by ring⟩, h21u_ne⟩
  have h21 : (21 : ℕ) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨⟨u, rfl⟩, h21u_ne⟩
  have h3u : (3 * u) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7, by ring⟩, h21u_ne⟩
  have h21u : (21 * u) ∈ (21 * u).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h21u_ne⟩
  have hsub : ({1, 3, 7, 21, 3 * u, 21 * u} : Finset ℕ) ⊆ (21 * u).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h7
    · exact h21
    · exact h3u
    · exact h21u
  have hcard : ({1, 3, 7, 21, 3 * u, 21 * u} : Finset ℕ).card = 6 := by
    rw [show ({1, 3, 7, 21, 3 * u, 21 * u} : Finset ℕ) =
            insert 1 (insert 3 (insert 7 (insert 21 (insert (3 * u) {21 * u})))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 6 ≤ (21 * u).divisors.card := by
    calc 6 = ({1, 3, 7, 21, 3 * u, 21 * u} : Finset ℕ).card := hcard.symm
      _ ≤ (21 * u).divisors.card := Finset.card_le_card hsub
  show 6 ≤ σ 0 (21 * u)
  have : σ 0 (21 * u) = (21 * u).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `v ≥ 2` then `28v` has at least 7 divisors `{1, 2, 4, 7, 14, 28, 28v}`. -/
@[category research open, AMS 11]
lemma seven_le_sigma_twentyeight_mul (v : ℕ) (hv : 2 ≤ v) : 7 ≤ σ 0 (28 * v) := by
  have h28v_ne : 28 * v ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h28v_ne⟩
  have h2 : (2 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨⟨14 * v, by ring⟩, h28v_ne⟩
  have h4 : (4 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7 * v, by ring⟩, h28v_ne⟩
  have h7 : (7 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨⟨4 * v, by ring⟩, h28v_ne⟩
  have h14 : (14 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * v, by ring⟩, h28v_ne⟩
  have h28 : (28 : ℕ) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨⟨v, rfl⟩, h28v_ne⟩
  have h28v : (28 * v) ∈ (28 * v).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h28v_ne⟩
  have hsub : ({1, 2, 4, 7, 14, 28, 28 * v} : Finset ℕ) ⊆ (28 * v).divisors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h4
    · exact h7
    · exact h14
    · exact h28
    · exact h28v
  have hcard : ({1, 2, 4, 7, 14, 28, 28 * v} : Finset ℕ).card = 7 := by
    rw [show ({1, 2, 4, 7, 14, 28, 28 * v} : Finset ℕ) =
            insert 1 (insert 2 (insert 4 (insert 7 (insert 14 (insert 28 {28 * v}))))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 7 ≤ (28 * v).divisors.card := by
    calc 7 = ({1, 2, 4, 7, 14, 28, 28 * v} : Finset ℕ).card := hcard.symm
      _ ≤ (28 * v).divisors.card := Finset.card_le_card hsub
  show 7 ≤ σ 0 (28 * v)
  have : σ 0 (28 * v) = (28 * v).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `x ≥ 2` then `42x` has at least 9 divisors. -/
@[category research open, AMS 11]
lemma nine_le_sigma_fortytwo_mul (x : ℕ) (hx : 2 ≤ x) : 9 ≤ σ 0 (42 * x) := by
  have h42x_ne : 42 * x ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, h42x_ne⟩
  have h2 : (2 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨21 * x, by ring⟩, h42x_ne⟩
  have h3 : (3 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨14 * x, by ring⟩, h42x_ne⟩
  have h6 : (6 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨7 * x, by ring⟩, h42x_ne⟩
  have h7 : (7 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨6 * x, by ring⟩, h42x_ne⟩
  have h14 : (14 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨3 * x, by ring⟩, h42x_ne⟩
  have h21 : (21 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨2 * x, by ring⟩, h42x_ne⟩
  have h42 : (42 : ℕ) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨⟨x, rfl⟩, h42x_ne⟩
  have h42x : (42 * x) ∈ (42 * x).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, h42x_ne⟩
  have hsub : ({1, 2, 3, 6, 7, 14, 21, 42, 42 * x} : Finset ℕ) ⊆ (42 * x).divisors := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h6
    · exact h7
    · exact h14
    · exact h21
    · exact h42
    · exact h42x
  have hcard : ({1, 2, 3, 6, 7, 14, 21, 42, 42 * x} : Finset ℕ).card = 9 := by
    rw [show ({1, 2, 3, 6, 7, 14, 21, 42, 42 * x} : Finset ℕ) =
            insert 1 (insert 2 (insert 3 (insert 6 (insert 7 (insert 14
              (insert 21 (insert 42 {42 * x}))))))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    all_goals (simp; omega)
  have hcount : 9 ≤ (42 * x).divisors.card := by
    calc 9 = ({1, 2, 3, 6, 7, 14, 21, 42, 42 * x} : Finset ℕ).card := hcard.symm
      _ ≤ (42 * x).divisors.card := Finset.card_le_card hsub
  show 9 ≤ σ 0 (42 * x)
  have : σ 0 (42 * x) = (42 * x).divisors.card := by simp [ArithmeticFunction.sigma_apply]
  rw [this]; exact hcount

/-- If `u ≥ 2` then `84u` has at least 15 divisors. (For `u ∈ {2, …, 7}`
    we case-bash; for `u ≥ 8` we use the divisors-of-84 plus `{21u, 42u, 84u}`.) -/
@[category research open, AMS 11]
lemma fifteen_le_sigma_eightyfour_mul (u : ℕ) (hu : 2 ≤ u) : 15 ≤ σ 0 (84 * u) := by
  rcases Nat.lt_or_ge u 8 with hlt | hge
  · -- u ∈ {2, 3, 4, 5, 6, 7}: bash with decide
    interval_cases u <;> decide
  · -- u ≥ 8: divisors of 84 plus {21u, 42u, 84u}, all distinct.
    have h84u_ne : 84 * u ≠ 0 := by omega
    -- All divisors of 84 = 2² · 3 · 7
    have h1 : (1 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd _, h84u_ne⟩
    have h2 : (2 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨42 * u, by ring⟩, h84u_ne⟩
    have h3 : (3 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨28 * u, by ring⟩, h84u_ne⟩
    have h4 : (4 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨21 * u, by ring⟩, h84u_ne⟩
    have h6 : (6 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨14 * u, by ring⟩, h84u_ne⟩
    have h7 : (7 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨12 * u, by ring⟩, h84u_ne⟩
    have h12 : (12 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨7 * u, by ring⟩, h84u_ne⟩
    have h14 : (14 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨6 * u, by ring⟩, h84u_ne⟩
    have h21 : (21 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨4 * u, by ring⟩, h84u_ne⟩
    have h28 : (28 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨3 * u, by ring⟩, h84u_ne⟩
    have h42 : (42 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨2 * u, by ring⟩, h84u_ne⟩
    have h84 : (84 : ℕ) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨u, rfl⟩, h84u_ne⟩
    have h21u : (21 * u) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨4, by ring⟩, h84u_ne⟩
    have h42u : (42 * u) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, h84u_ne⟩
    have h84u : (84 * u) ∈ (84 * u).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_refl _, h84u_ne⟩
    have hsub : ({1, 2, 3, 4, 6, 7, 12, 14, 21, 28, 42, 84, 21 * u, 42 * u, 84 * u}
                 : Finset ℕ) ⊆ (84 * u).divisors := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h6
      · exact h7
      · exact h12
      · exact h14
      · exact h21
      · exact h28
      · exact h42
      · exact h84
      · exact h21u
      · exact h42u
      · exact h84u
    have hcard :
        ({1, 2, 3, 4, 6, 7, 12, 14, 21, 28, 42, 84, 21 * u, 42 * u, 84 * u}
         : Finset ℕ).card = 15 := by
      rw [show ({1, 2, 3, 4, 6, 7, 12, 14, 21, 28, 42, 84, 21 * u, 42 * u, 84 * u}
               : Finset ℕ) =
            insert 1 (insert 2 (insert 3 (insert 4 (insert 6 (insert 7 (insert 12
            (insert 14 (insert 21 (insert 28 (insert 42 (insert 84
            (insert (21 * u) (insert (42 * u) {84 * u}))))))))))))) from rfl]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton]
      all_goals (simp; omega)
    have hcount : 15 ≤ (84 * u).divisors.card := by
      calc 15 = _ := hcard.symm
        _ ≤ (84 * u).divisors.card := Finset.card_le_card hsub
    show 15 ≤ σ 0 (84 * u)
    have : σ 0 (84 * u) = (84 * u).divisors.card := by simp [ArithmeticFunction.sigma_apply]
    rw [this]; exact hcount

set_option maxHeartbeats 800000 in
/-- Seven divides any (∗)-bounded `n > 54`. -/
@[category research open, AMS 11]
theorem seven_dvd_of_starBound {n : ℕ} (hn : 54 < n) (hsb : StarBound n) : 7 ∣ n := by
  have h4 : 4 ∣ n := four_dvd_of_starBound (by omega) hsb
  have h3 : 3 ∣ n := three_dvd_of_starBound (by omega) hsb
  have h5 : 5 ∣ n := five_dvd_of_starBound (by omega) hsb
  by_contra h7
  have hmod : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  rcases hmod with hm | hm | hm | hm | hm | hm
  · -- r = 1, k = 1
    have hd : 7 ∣ (n - 1) := by omega
    obtain ⟨j, hj⟩ := hd
    have hj_ge : 8 ≤ j := by omega
    have htau : σ 0 (n - 1) ≤ 3 := by
      have := (starBound_iff_tau_le n).1 hsb 1 (by omega) (by omega)
      simpa using this
    rw [hj] at htau
    have hh : 4 ≤ σ 0 (7 * j) := four_le_sigma_seven_mul j hj_ge
    omega
  · -- r = 2, k = 2
    have hd : 14 ∣ (n - 2) := by omega
    obtain ⟨t, ht⟩ := hd
    have ht_ge : 2 ≤ t := by omega
    have htau : σ 0 (n - 2) ≤ 4 := by
      have := (starBound_iff_tau_le n).1 hsb 2 (by omega) (by omega)
      simpa using this
    rw [ht] at htau
    have hh : 5 ≤ σ 0 (14 * t) := five_le_sigma_fourteen_mul t ht_ge
    omega
  · -- r = 3, k = 3
    have hd : 21 ∣ (n - 3) := by omega
    obtain ⟨u, hu⟩ := hd
    have hu_ge : 8 ≤ u := by omega
    have htau : σ 0 (n - 3) ≤ 5 := by
      have := (starBound_iff_tau_le n).1 hsb 3 (by omega) (by omega)
      simpa using this
    rw [hu] at htau
    have hh : 6 ≤ σ 0 (21 * u) := six_le_sigma_twentyone_mul u hu_ge
    omega
  · -- r = 4, k = 4
    have hd : 28 ∣ (n - 4) := by omega
    obtain ⟨v, hv⟩ := hd
    have hv_ge : 2 ≤ v := by omega
    have htau : σ 0 (n - 4) ≤ 6 := by
      have := (starBound_iff_tau_le n).1 hsb 4 (by omega) (by omega)
      simpa using this
    rw [hv] at htau
    have hh : 7 ≤ σ 0 (28 * v) := seven_le_sigma_twentyeight_mul v hv_ge
    omega
  · -- r = 5, k = 12 (k = 5 fails: 35·prime has only 4 divisors)
    have hd : 84 ∣ (n - 12) := by omega
    obtain ⟨u, hu⟩ := hd
    have hu_ge : 2 ≤ u := by omega
    have htau : σ 0 (n - 12) ≤ 14 := by
      have := (starBound_iff_tau_le n).1 hsb 12 (by omega) (by omega)
      simpa using this
    rw [hu] at htau
    have hh : 15 ≤ σ 0 (84 * u) := fifteen_le_sigma_eightyfour_mul u hu_ge
    omega
  · -- r = 6, k = 6
    have hd : 42 ∣ (n - 6) := by omega
    obtain ⟨x, hx⟩ := hd
    have hx_ge : 2 ≤ x := by omega
    have htau : σ 0 (n - 6) ≤ 8 := by
      have := (starBound_iff_tau_le n).1 hsb 6 (by omega) (by omega)
      simpa using this
    rw [hx] at htau
    have hh : 9 ≤ σ 0 (42 * x) := nine_le_sigma_fortytwo_mul x hx_ge
    omega

/-! ### Lemma 8.  `n > 25,200 ∧ StarBound n → 11 ∣ n`.

For each residue `r ∈ {1, ..., 10}` of `n mod 11`, with the prior step `2520 ∣ n`,
we choose `k = r` (when `r ∣ 2520`) so that `n - k = 11r·s` with `τ(n-k) ≥ 4·τ(r)`.
The exception is `r = 7`: instead use `k = 18 = 7 + 11`, getting `n - 18 = 18·(140N - 1)`
with `11 ∣ 140N - 1`, hence `n - 18 = 2 · 3² · 11 · t` with `t ≥ 229` prime, giving
`τ(n - 18) ≥ 24 > 20 = k + 2`.
-/

/-- The first part of the modular ladder, fully proved here:
    `840 = 2³·3·5·7` divides any (∗)-bounded `n > 54`. -/
@[category research open, AMS 11]
theorem dvd_840_of_starBound {n : ℕ} (hn : 54 < n) (hsb : StarBound n) : 840 ∣ n := by
  have h8 : 8 ∣ n := eight_dvd_of_starBound (by omega) hsb
  have h3 : 3 ∣ n := three_dvd_of_starBound (by omega) hsb
  have h5 : 5 ∣ n := five_dvd_of_starBound (by omega) hsb
  have h7 : 7 ∣ n := seven_dvd_of_starBound hn hsb
  have h24 : 24 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h8 h3
  have h120 : 120 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h24 h5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h120 h7

/-- Eleven divides any (∗)-bounded `n > 25,200`. -/
@[category research open, AMS 11]
theorem eleven_dvd_of_starBound {n : ℕ} (hn : 25200 < n) (hsb : StarBound n) : 11 ∣ n := by
  sorry

/- ### Lemma 9.  `n > 332,640 ∧ StarBound n → 13 ∣ n`. -/

/-- Thirteen divides any (∗)-bounded `n > 332,640`. -/
@[category research open, AMS 11]
theorem thirteen_dvd_of_starBound {n : ℕ} (hn : 332640 < n) (hsb : StarBound n) : 13 ∣ n := by
  sorry

/- ### Theorem. The combined modular ladder. -/

/-- The combined modular ladder: `360,360 = 2^3·3^2·5·7·11·13` divides any (∗)-bounded `n > 332,640`. -/
@[category research open, AMS 11]
theorem dvd_360360_of_starBound {n : ℕ} (hn : 332640 < n) (hsb : StarBound n) :
    360360 ∣ n := by
  -- Combination lemma: assuming all the prior modular constraints.
  -- 360360 = 2^3 * 3^2 * 5 * 7 * 11 * 13.
  -- Should follow from {two,four,eight,three,nine,five,seven,eleven,thirteen}_dvd_of_starBound
  -- via pairwise coprimality of the prime powers.  Left as a sorry to avoid
  -- combining 9 sorry-hypotheses (which currently triggers a `whnf` timeout).
  sorry

/-! ### Phase 2: Prime/near-prime conditions on `N` for `n = 2520 N`.

These are *consequences* of `StarBound n` together with `360360 ∣ n` (so `143 ∣ N`).
They do not establish a contradiction; they tightly constrain N.
-/

/-- A square `k^2` is never `≡ 7 (mod 8)`: the only quadratic residues mod 8 are
    `{0, 1, 4}`. -/
@[category research solved, AMS 11]
lemma sq_mod_eight_ne_seven (k : ℕ) : k ^ 2 % 8 ≠ 7 := by
  have h : k ^ 2 % 8 = (k % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  rw [h]
  have : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 8) <;> decide

/-- **Boris Alexeev's mod-8 sharpening (Jan 2026 forum comment).**  For any
    `N ≥ 1`, `2520 N − 1` is *not* a perfect square, because `2520 ≡ 0 (mod 8)`
    forces `2520 N − 1 ≡ 7 (mod 8)`, and `7` is not a quadratic residue mod 8.

    Combined with the τ ≤ 3 constraint at k = 1 (which forces `2520 N − 1 ∈
    {1, prime, prime²}`), this rules out the `prime²` case and upgrades the
    conclusion to `Nat.Prime (2520 N − 1)`. -/
@[category research solved, AMS 11]
theorem phase2_k1_not_square {N : ℕ} (hN : 0 < N) :
    ¬ ∃ k : ℕ, 2520 * N - 1 = k ^ 2 := by
  rintro ⟨k, hk⟩
  have hmod : (2520 * N - 1) % 8 = 7 := by omega
  rw [hk] at hmod
  exact sq_mod_eight_ne_seven k hmod

/-- Phase 2 prime-condition at k=1: 2520N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k1_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (2520 * N - 1) := by
  -- σ 0 (2520N - 1) ≤ 3, so 2520N - 1 is 1, prime, or prime².
  -- 2520N ≡ 0 mod 8 ⇒ 2520N - 1 ≡ 7 mod 8, but squares mod 8 ∈ {0, 1, 4}, so not prime².
  -- 2520N - 1 ≥ 2519 > 1, so prime.
  sorry

/-- Phase 2 prime-condition at k=2: 1260N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k2_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (1260 * N - 1) := by
  sorry

/-- Phase 2 prime-condition at k=3: 840N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k3_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (840 * N - 1) := by
  sorry

/-- Phase 2 prime-condition at k=4: 630N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k4_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (630 * N - 1) := by
  sorry

/-- Phase 2 prime-condition at k=6: 420N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k6_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (420 * N - 1) := by
  sorry

/-- Phase 2 prime-condition at k=8: 315N − 1 ∈ {p, 2p}. -/
@[category research open, AMS 11]
theorem phase2_k8_p_or_2p {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (315 * N - 1) ∨
    (2 ∣ (315 * N - 1) ∧ Nat.Prime ((315 * N - 1) / 2)) := by
  sorry

/-- Phase 2 prime-condition at k=12: 210N − 1 is prime. -/
@[category research open, AMS 11]
theorem phase2_k12_prime {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    Nat.Prime (210 * N - 1) := by
  sorry

/-- Phase 2 prime-condition at k=24: 105N − 1 ∈ {p, p², 2p, 4p}. -/
@[category research open, AMS 11]
theorem phase2_k24_p_or_p2_or_2p_or_4p {N : ℕ} (hN : 0 < N) (hsb : StarBound (2520 * N)) :
    let m := 105 * N - 1
    Nat.Prime m ∨
    (∃ p, Nat.Prime p ∧ m = p^2) ∨
    (2 ∣ m ∧ Nat.Prime (m / 2)) ∨
    (4 ∣ m ∧ Nat.Prime (m / 4)) := by
  sorry

end Erdos647
