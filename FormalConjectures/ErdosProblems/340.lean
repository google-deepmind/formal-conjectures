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

/-!
# Erdős Problem 340

*Reference:* [erdosproblems.com/340](https://www.erdosproblems.com/340)
-/

open Filter Finset
open scoped Real Pointwise

set_option maxHeartbeats 800000

namespace Erdos340

/-- Given a finite Sidon set `A` and a lower bound `m`, `go` finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. If `A` is empty then this returns the value `m`. Note that
the lower bound is required to avoid `0` being a contender in some cases. -/
def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    haveI : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using hA.exists_insert_ge h m
    ⟨Nat.find this, Nat.find_spec this⟩
  else ⟨m, by simp_all [IsSidon]⟩

/-- Main search loop for generating the greedy Sidon sequence. -/
def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A ∪ {s'.1}, s'.2.2.2⟩, s')

/-- `greedySidon` is the greedy Sidon sequence starting from `{1}`. -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

private lemma go_val_irrel {A : Finset ℕ} (hA hA' : IsSidon (A : Set ℕ)) (m : ℕ) :
    (greedySidon.go A hA m).1 = (greedySidon.go A hA' m).1 := by
  simp only [greedySidon.go]

private lemma go_set_eq {A B : Finset ℕ} (hAB : A = B)
    (hA : IsSidon (A : Set ℕ)) (hB : IsSidon (B : Set ℕ)) (m : ℕ) :
    (greedySidon.go A hA m).1 = (greedySidon.go B hB m).1 := by
  cases hAB; exact go_val_irrel hA hB m

private lemma go_eq_val {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) {m v : ℕ}
    (hNE : A.Nonempty)
    (hv_ge : v ≥ m)
    (hv_nmem : v ∉ A)
    (hv_sidon : IsSidon (↑(A ∪ {v}) : Set ℕ))
    (hv_min : ∀ k, m ≤ k → k < v → k ∈ A ∨ ¬IsSidon (↑(A ∪ {k}) : Set ℕ)) :
    (greedySidon.go A hA m).1 = v := by
  simp only [greedySidon.go, dif_pos hNE]
  rw [Nat.find_eq_iff]
  refine ⟨⟨hv_ge, hv_nmem, hv_sidon⟩, fun k hkv => ?_⟩
  rintro ⟨hkge, hknmem, hksidon⟩
  rcases hv_min k hkge hkv with hkmem | hknotsidon
  · exact hknmem hkmem
  · exact hknotsidon hksidon

private lemma aux_succ_set_eq (k : ℕ) :
    (greedySidon.aux (k + 1)).1.1 =
      (greedySidon.aux k).1.1 ∪ {(greedySidon.aux (k + 1)).2} := rfl

private lemma aux_0_set : (greedySidon.aux 0).1.1 = {1} := rfl
private lemma aux_0_val : (greedySidon.aux 0).2 = 1 := rfl

private lemma go_step1 (hA : IsSidon (({1} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1} hA 2).1 = 2 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by omega)

private lemma aux_1_val : (greedySidon.aux 1).2 = 2 := by
  rw [show (greedySidon.aux 1).2 =
      (greedySidon.go (greedySidon.aux 0).1.1 (greedySidon.aux 0).1.2 2).1 from rfl]
  rw [go_val_irrel (greedySidon.aux 0).1.2
    (show IsSidon (({1} : Finset ℕ) : Set ℕ) from by decide)]
  exact go_step1 _

private lemma aux_1_set : (greedySidon.aux 1).1.1 = {1, 2} := by
  rw [aux_succ_set_eq, aux_0_set, aux_1_val]; decide


private lemma go_step2 (hA : IsSidon (({1, 2} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2} hA 3).1 = 4 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkval : k = 3 := by omega
      subst hkval
      right; intro hsidon
      have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 3 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
      simp only [show (1:ℕ) = 2 ↔ False from by decide, show (3:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (3:ℕ) = 2 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_2_val : (greedySidon.aux 2).2 = 4 := by
  have h1s := aux_1_set
  have hNE : (greedySidon.aux 1).1.1.Nonempty :=
    h1s ▸ (by decide : ({1, 2} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 2).2 =
      (greedySidon.go (greedySidon.aux 1).1.1 (greedySidon.aux 1).1.2
        (if h : (greedySidon.aux 1).1.1.Nonempty then
          (greedySidon.aux 1).1.1.max' h + 1 else (greedySidon.aux 1).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 1).1.1.max' hNE = 2 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2} : Finset ℕ) := h1s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h1s ▸ (by decide : (2 : ℕ) ∈ ({1, 2} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h1s _ hB]
  exact go_step2 hB

private lemma aux_2_set : (greedySidon.aux 2).1.1 = {1, 2, 4} := by
  rw [aux_succ_set_eq, aux_1_set, aux_2_val]; decide

private lemma go_step3 (hA : IsSidon (({1, 2, 4} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4} hA 5).1 = 8 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 5 7 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 5: 1+5 = 4+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 5 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 4 ↔ False from by decide, show (5:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (5:ℕ) = 4 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 6: 2+6 = 4+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 6 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 4 ↔ False from by decide, show (6:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (6:ℕ) = 4 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 7: 1+7 = 4+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 7 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 4 ↔ False from by decide, show (7:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (7:ℕ) = 4 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_3_val : (greedySidon.aux 3).2 = 8 := by
  have h2s := aux_2_set
  have hNE : (greedySidon.aux 2).1.1.Nonempty :=
    h2s ▸ (by decide : ({1, 2, 4} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 3).2 =
      (greedySidon.go (greedySidon.aux 2).1.1 (greedySidon.aux 2).1.2
        (if h : (greedySidon.aux 2).1.1.Nonempty then
          (greedySidon.aux 2).1.1.max' h + 1 else (greedySidon.aux 2).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 2).1.1.max' hNE = 4 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4} : Finset ℕ) := h2s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h2s ▸ (by decide : (4 : ℕ) ∈ ({1, 2, 4} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h2s _ hB]
  exact go_step3 hB

private lemma aux_3_set : (greedySidon.aux 3).1.1 = {1, 2, 4, 8} := by
  rw [aux_succ_set_eq, aux_2_set, aux_3_val]; decide

private lemma go_step4 (hA : IsSidon (({1, 2, 4, 8} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8} hA 9).1 = 13 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 9 12 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 9: 1+9 = 8+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 9 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 8 ↔ False from by decide, show (9:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (9:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 10: 2+10 = 8+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 10 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 8 ↔ False from by decide, show (10:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (10:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 11: 1+11 = 8+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 11 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 8 ↔ False from by decide, show (11:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (11:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 12: 4+12 = 8+8
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 12 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 8 ↔ False from by decide, show (12:ℕ) = 8 ↔ False from by decide, show (4:ℕ) = 8 ↔ False from by decide, show (12:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_4_val : (greedySidon.aux 4).2 = 13 := by
  have h3s := aux_3_set
  have hNE : (greedySidon.aux 3).1.1.Nonempty :=
    h3s ▸ (by decide : ({1, 2, 4, 8} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 4).2 =
      (greedySidon.go (greedySidon.aux 3).1.1 (greedySidon.aux 3).1.2
        (if h : (greedySidon.aux 3).1.1.Nonempty then
          (greedySidon.aux 3).1.1.max' h + 1 else (greedySidon.aux 3).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 3).1.1.max' hNE = 8 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8} : Finset ℕ) := h3s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h3s ▸ (by decide : (8 : ℕ) ∈ ({1, 2, 4, 8} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h3s _ hB]
  exact go_step4 hB

private lemma aux_4_set : (greedySidon.aux 4).1.1 = {1, 2, 4, 8, 13} := by
  rw [aux_succ_set_eq, aux_3_set, aux_4_val]; decide

private lemma go_step5 (hA : IsSidon (({1, 2, 4, 8, 13} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13} hA 14).1 = 21 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 14 20 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 14: 1+14 = 13+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 14 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 13 ↔ False from by decide, show (14:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (14:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 15: 1+15 = 8+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 15 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 8 ↔ False from by decide, show (15:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (15:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 16: 1+16 = 13+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 16 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 13 ↔ False from by decide, show (16:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (16:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 17: 4+17 = 13+8
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 17 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 13 ↔ False from by decide, show (17:ℕ) = 8 ↔ False from by decide, show (4:ℕ) = 8 ↔ False from by decide, show (17:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 18: 8+18 = 13+13
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 18 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 13 ↔ False from by decide, show (18:ℕ) = 13 ↔ False from by decide, show (8:ℕ) = 13 ↔ False from by decide, show (18:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 19: 2+19 = 13+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 19 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 13 ↔ False from by decide, show (19:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (19:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 20: 1+20 = 13+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 20 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 13 ↔ False from by decide, show (20:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (20:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_5_val : (greedySidon.aux 5).2 = 21 := by
  have h4s := aux_4_set
  have hNE : (greedySidon.aux 4).1.1.Nonempty :=
    h4s ▸ (by decide : ({1, 2, 4, 8, 13} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 5).2 =
      (greedySidon.go (greedySidon.aux 4).1.1 (greedySidon.aux 4).1.2
        (if h : (greedySidon.aux 4).1.1.Nonempty then
          (greedySidon.aux 4).1.1.max' h + 1 else (greedySidon.aux 4).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 4).1.1.max' hNE = 13 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13} : Finset ℕ) := h4s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h4s ▸ (by decide : (13 : ℕ) ∈ ({1, 2, 4, 8, 13} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h4s _ hB]
  exact go_step5 hB

private lemma aux_5_set : (greedySidon.aux 5).1.1 = {1, 2, 4, 8, 13, 21} := by
  rw [aux_succ_set_eq, aux_4_set, aux_5_val]; decide

private lemma go_step6 (hA : IsSidon (({1, 2, 4, 8, 13, 21} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21} hA 22).1 = 31 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 22 30 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 22: 1+22 = 21+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 22 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (22:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (22:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 23: 2+23 = 21+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 23 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 21 ↔ False from by decide, show (23:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (23:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 24: 1+24 = 21+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 24 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (24:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (24:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 25: 1+25 = 13+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 25 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 13 ↔ False from by decide, show (25:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (25:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 26: 8+26 = 21+13
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 26 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 21 ↔ False from by decide, show (26:ℕ) = 13 ↔ False from by decide, show (8:ℕ) = 13 ↔ False from by decide, show (26:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 27: 2+27 = 21+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 27 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 21 ↔ False from by decide, show (27:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (27:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 28: 1+28 = 21+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 28 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (28:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (28:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 29: 13+29 = 21+21
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 29 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 21 ↔ False from by decide, show (29:ℕ) = 21 ↔ False from by decide, show (13:ℕ) = 21 ↔ False from by decide, show (29:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 30: 4+30 = 21+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 30 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 21 ↔ False from by decide, show (30:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (30:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_6_val : (greedySidon.aux 6).2 = 31 := by
  have h5s := aux_5_set
  have hNE : (greedySidon.aux 5).1.1.Nonempty :=
    h5s ▸ (by decide : ({1, 2, 4, 8, 13, 21} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 6).2 =
      (greedySidon.go (greedySidon.aux 5).1.1 (greedySidon.aux 5).1.2
        (if h : (greedySidon.aux 5).1.1.Nonempty then
          (greedySidon.aux 5).1.1.max' h + 1 else (greedySidon.aux 5).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 5).1.1.max' hNE = 21 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21} : Finset ℕ) := h5s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h5s ▸ (by decide : (21 : ℕ) ∈ ({1, 2, 4, 8, 13, 21} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h5s _ hB]
  exact go_step6 hB

private lemma aux_6_set : (greedySidon.aux 6).1.1 = {1, 2, 4, 8, 13, 21, 31} := by
  rw [aux_succ_set_eq, aux_5_set, aux_6_val]; decide

private lemma go_step7 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31} hA 32).1 = 45 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 32 44 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 32: 1+32 = 31+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 32 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (32:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (32:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 33: 1+33 = 21+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 33 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (33:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (33:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 34: 1+34 = 31+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 34 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (34:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (34:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 35: 4+35 = 31+8
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 35 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 31 ↔ False from by decide, show (35:ℕ) = 8 ↔ False from by decide, show (4:ℕ) = 8 ↔ False from by decide, show (35:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 36: 8+36 = 31+13
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 36 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 31 ↔ False from by decide, show (36:ℕ) = 13 ↔ False from by decide, show (8:ℕ) = 13 ↔ False from by decide, show (36:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 37: 2+37 = 31+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 37 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 31 ↔ False from by decide, show (37:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (37:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 38: 1+38 = 31+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 38 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (38:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (38:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 39: 13+39 = 31+21
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 39 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 31 ↔ False from by decide, show (39:ℕ) = 21 ↔ False from by decide, show (13:ℕ) = 21 ↔ False from by decide, show (39:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 40: 2+40 = 21+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 40 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 21 ↔ False from by decide, show (40:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (40:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 41: 1+41 = 21+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 41 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (41:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (41:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 42: 2+42 = 31+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 42 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 31 ↔ False from by decide, show (42:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (42:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 43: 1+43 = 31+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 43 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (43:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (43:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 44: 8+44 = 31+21
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 44 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 31 ↔ False from by decide, show (44:ℕ) = 21 ↔ False from by decide, show (8:ℕ) = 21 ↔ False from by decide, show (44:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_7_val : (greedySidon.aux 7).2 = 45 := by
  have h6s := aux_6_set
  have hNE : (greedySidon.aux 6).1.1.Nonempty :=
    h6s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 7).2 =
      (greedySidon.go (greedySidon.aux 6).1.1 (greedySidon.aux 6).1.2
        (if h : (greedySidon.aux 6).1.1.Nonempty then
          (greedySidon.aux 6).1.1.max' h + 1 else (greedySidon.aux 6).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 6).1.1.max' hNE = 31 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31} : Finset ℕ) := h6s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h6s ▸ (by decide : (31 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h6s _ hB]
  exact go_step7 hB

private lemma aux_7_set : (greedySidon.aux 7).1.1 = {1, 2, 4, 8, 13, 21, 31, 45} := by
  rw [aux_succ_set_eq, aux_6_set, aux_7_val]; decide

private lemma go_step8 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45} hA 46).1 = 66 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 46 65 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 46: 1+46 = 45+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 46 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (46:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (46:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 47: 2+47 = 45+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 47 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 45 ↔ False from by decide, show (47:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (47:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 48: 1+48 = 45+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 48 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (48:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (48:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 49: 4+49 = 45+8
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 49 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 45 ↔ False from by decide, show (49:ℕ) = 8 ↔ False from by decide, show (4:ℕ) = 8 ↔ False from by decide, show (49:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 50: 2+50 = 31+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 50 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 31 ↔ False from by decide, show (50:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (50:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 51: 1+51 = 31+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 51 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (51:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (51:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 52: 1+52 = 45+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 52 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (52:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (52:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 53: 13+53 = 45+21
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 53 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 45 ↔ False from by decide, show (53:ℕ) = 21 ↔ False from by decide, show (13:ℕ) = 21 ↔ False from by decide, show (53:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 54: 4+54 = 45+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 54 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 45 ↔ False from by decide, show (54:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (54:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 55: 21+55 = 45+31
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 55 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 45 ↔ False from by decide, show (55:ℕ) = 31 ↔ False from by decide, show (21:ℕ) = 31 ↔ False from by decide, show (55:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 56: 2+56 = 45+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 56 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 45 ↔ False from by decide, show (56:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (56:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 57: 1+57 = 45+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 57 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (57:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (57:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 58: 4+58 = 31+31
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 58 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 31 ↔ False from by decide, show (58:ℕ) = 31 ↔ False from by decide, show (4:ℕ) = 31 ↔ False from by decide, show (58:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 59: 31+59 = 45+45
        right; intro hsidon
        have hcontra := hsidon 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 59 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (31:ℕ) = 45 ↔ False from by decide, show (59:ℕ) = 45 ↔ False from by decide, show (31:ℕ) = 45 ↔ False from by decide, show (59:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 60: 2+60 = 31+31
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 60 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 31 ↔ False from by decide, show (60:ℕ) = 31 ↔ False from by decide, show (2:ℕ) = 31 ↔ False from by decide, show (60:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 61: 1+61 = 31+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 61 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 31 ↔ False from by decide, show (61:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (61:ℕ) = 31 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 62: 4+62 = 45+21
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 62 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 45 ↔ False from by decide, show (62:ℕ) = 21 ↔ False from by decide, show (4:ℕ) = 21 ↔ False from by decide, show (62:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 63: 13+63 = 45+31
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 63 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 45 ↔ False from by decide, show (63:ℕ) = 31 ↔ False from by decide, show (13:ℕ) = 31 ↔ False from by decide, show (63:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 64: 2+64 = 45+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 64 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 45 ↔ False from by decide, show (64:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (64:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 65: 1+65 = 45+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 65 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (65:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (65:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_8_val : (greedySidon.aux 8).2 = 66 := by
  have h7s := aux_7_set
  have hNE : (greedySidon.aux 7).1.1.Nonempty :=
    h7s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 8).2 =
      (greedySidon.go (greedySidon.aux 7).1.1 (greedySidon.aux 7).1.2
        (if h : (greedySidon.aux 7).1.1.Nonempty then
          (greedySidon.aux 7).1.1.max' h + 1 else (greedySidon.aux 7).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 7).1.1.max' hNE = 45 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45} : Finset ℕ) := h7s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h7s ▸ (by decide : (45 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h7s _ hB]
  exact go_step8 hB

private lemma aux_8_set : (greedySidon.aux 8).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66} := by
  rw [aux_succ_set_eq, aux_7_set, aux_8_val]; decide

private lemma go_step9 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66} hA 67).1 = 81 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 67 80 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 67: 1+67 = 66+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 67 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (67:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (67:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 68: 2+68 = 66+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 68 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (68:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (68:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 69: 1+69 = 66+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 69 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (69:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (69:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 70: 4+70 = 66+8
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 70 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 66 ↔ False from by decide, show (70:ℕ) = 8 ↔ False from by decide, show (4:ℕ) = 8 ↔ False from by decide, show (70:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 71: 8+71 = 66+13
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 71 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 66 ↔ False from by decide, show (71:ℕ) = 13 ↔ False from by decide, show (8:ℕ) = 13 ↔ False from by decide, show (71:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 72: 2+72 = 66+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 72 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (72:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (72:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 73: 1+73 = 66+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 73 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (73:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (73:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 74: 2+74 = 45+31
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 74 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 45 ↔ False from by decide, show (74:ℕ) = 31 ↔ False from by decide, show (2:ℕ) = 31 ↔ False from by decide, show (74:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 75: 1+75 = 45+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 75 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (75:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (75:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 76: 21+76 = 66+31
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 76 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 66 ↔ False from by decide, show (76:ℕ) = 31 ↔ False from by decide, show (21:ℕ) = 31 ↔ False from by decide, show (76:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 77: 2+77 = 66+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 77 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (77:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (77:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 78: 1+78 = 66+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 78 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (78:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (78:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 79: 8+79 = 66+21
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 79 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 66 ↔ False from by decide, show (79:ℕ) = 21 ↔ False from by decide, show (8:ℕ) = 21 ↔ False from by decide, show (79:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 80: 31+80 = 66+45
        right; intro hsidon
        have hcontra := hsidon 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 80 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (31:ℕ) = 66 ↔ False from by decide, show (80:ℕ) = 45 ↔ False from by decide, show (31:ℕ) = 45 ↔ False from by decide, show (80:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_9_val : (greedySidon.aux 9).2 = 81 := by
  have h8s := aux_8_set
  have hNE : (greedySidon.aux 8).1.1.Nonempty :=
    h8s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 9).2 =
      (greedySidon.go (greedySidon.aux 8).1.1 (greedySidon.aux 8).1.2
        (if h : (greedySidon.aux 8).1.1.Nonempty then
          (greedySidon.aux 8).1.1.max' h + 1 else (greedySidon.aux 8).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 8).1.1.max' hNE = 66 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66} : Finset ℕ) := h8s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h8s ▸ (by decide : (66 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h8s _ hB]
  exact go_step9 hB

private lemma aux_9_set : (greedySidon.aux 9).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81} := by
  rw [aux_succ_set_eq, aux_8_set, aux_9_val]; decide

private lemma go_step10 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66, 81} hA 82).1 = 97 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 82 96 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 82: 1+82 = 81+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 82 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (82:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (82:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 83: 2+83 = 81+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 83 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 81 ↔ False from by decide, show (83:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (83:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 84: 1+84 = 81+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 84 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (84:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (84:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 85: 2+85 = 66+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 85 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (85:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (85:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 86: 1+86 = 66+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 86 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (86:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (86:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 87: 2+87 = 81+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 87 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 81 ↔ False from by decide, show (87:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (87:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 88: 1+88 = 81+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 88 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (88:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (88:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 89: 1+89 = 45+45
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 89 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (89:ℕ) = 45 ↔ False from by decide, show (1:ℕ) = 45 ↔ False from by decide, show (89:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 90: 4+90 = 81+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 90 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 81 ↔ False from by decide, show (90:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (90:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 91: 21+91 = 81+31
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 91 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 81 ↔ False from by decide, show (91:ℕ) = 31 ↔ False from by decide, show (21:ℕ) = 31 ↔ False from by decide, show (91:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 92: 2+92 = 81+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 92 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 81 ↔ False from by decide, show (92:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (92:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 93: 1+93 = 81+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 93 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (93:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (93:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 94: 8+94 = 81+21
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 94 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 81 ↔ False from by decide, show (94:ℕ) = 21 ↔ False from by decide, show (8:ℕ) = 21 ↔ False from by decide, show (94:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 95: 2+95 = 66+31
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 95 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (95:ℕ) = 31 ↔ False from by decide, show (2:ℕ) = 31 ↔ False from by decide, show (95:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 96: 1+96 = 66+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 96 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (96:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (96:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_10_val : (greedySidon.aux 10).2 = 97 := by
  have h9s := aux_9_set
  have hNE : (greedySidon.aux 9).1.1.Nonempty :=
    h9s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 10).2 =
      (greedySidon.go (greedySidon.aux 9).1.1 (greedySidon.aux 9).1.2
        (if h : (greedySidon.aux 9).1.1.Nonempty then
          (greedySidon.aux 9).1.1.max' h + 1 else (greedySidon.aux 9).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 9).1.1.max' hNE = 81 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81} : Finset ℕ) := h9s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h9s ▸ (by decide : (81 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h9s _ hB]
  exact go_step10 hB

private lemma aux_10_set : (greedySidon.aux 10).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} := by
  rw [aux_succ_set_eq, aux_9_set, aux_10_val]; decide

private lemma go_step11 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} hA 98).1 = 123 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 98 122 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 98: 1+98 = 97+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 98 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (98:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (98:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 99: 2+99 = 97+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 99 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (99:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (99:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 100: 1+100 = 97+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 100 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (100:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (100:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 101: 1+101 = 81+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 101 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (101:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (101:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 102: 8+102 = 97+13
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 102 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 97 ↔ False from by decide, show (102:ℕ) = 13 ↔ False from by decide, show (8:ℕ) = 13 ↔ False from by decide, show (102:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 103: 2+103 = 97+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 103 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (103:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (103:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 104: 1+104 = 97+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 104 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (104:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (104:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 105: 13+105 = 97+21
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 105 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 97 ↔ False from by decide, show (105:ℕ) = 21 ↔ False from by decide, show (13:ℕ) = 21 ↔ False from by decide, show (105:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 106: 4+106 = 97+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 106 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 97 ↔ False from by decide, show (106:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (106:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 107: 4+107 = 66+45
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 107 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 66 ↔ False from by decide, show (107:ℕ) = 45 ↔ False from by decide, show (4:ℕ) = 45 ↔ False from by decide, show (107:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 108: 2+108 = 97+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 108 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (108:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (108:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 109: 1+109 = 97+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 109 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (109:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (109:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 110: 1+110 = 66+45
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 110 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (110:ℕ) = 45 ↔ False from by decide, show (1:ℕ) = 45 ↔ False from by decide, show (110:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 111: 1+111 = 81+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 111 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (111:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (111:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 112: 66+112 = 97+81
        right; intro hsidon
        have hcontra := hsidon 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 112 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (66:ℕ) = 97 ↔ False from by decide, show (112:ℕ) = 81 ↔ False from by decide, show (66:ℕ) = 81 ↔ False from by decide, show (112:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 113: 13+113 = 81+45
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 113 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 81 ↔ False from by decide, show (113:ℕ) = 45 ↔ False from by decide, show (13:ℕ) = 45 ↔ False from by decide, show (113:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 114: 4+114 = 97+21
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 114 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 97 ↔ False from by decide, show (114:ℕ) = 21 ↔ False from by decide, show (4:ℕ) = 21 ↔ False from by decide, show (114:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 115: 13+115 = 97+31
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 115 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 97 ↔ False from by decide, show (115:ℕ) = 31 ↔ False from by decide, show (13:ℕ) = 31 ↔ False from by decide, show (115:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 116: 2+116 = 97+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 116 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (116:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (116:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 117: 1+117 = 97+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 117 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (117:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (117:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 118: 8+118 = 81+45
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 118 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 81 ↔ False from by decide, show (118:ℕ) = 45 ↔ False from by decide, show (8:ℕ) = 45 ↔ False from by decide, show (118:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 119: 13+119 = 66+66
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 119 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 66 ↔ False from by decide, show (119:ℕ) = 66 ↔ False from by decide, show (13:ℕ) = 66 ↔ False from by decide, show (119:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 120: 8+120 = 97+31
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 120 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 97 ↔ False from by decide, show (120:ℕ) = 31 ↔ False from by decide, show (8:ℕ) = 31 ↔ False from by decide, show (120:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 121: 21+121 = 97+45
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 121 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 97 ↔ False from by decide, show (121:ℕ) = 45 ↔ False from by decide, show (21:ℕ) = 45 ↔ False from by decide, show (121:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 122: 4+122 = 81+45
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 122 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 81 ↔ False from by decide, show (122:ℕ) = 45 ↔ False from by decide, show (4:ℕ) = 45 ↔ False from by decide, show (122:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_11_val : (greedySidon.aux 11).2 = 123 := by
  have h10s := aux_10_set
  have hNE : (greedySidon.aux 10).1.1.Nonempty :=
    h10s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 11).2 =
      (greedySidon.go (greedySidon.aux 10).1.1 (greedySidon.aux 10).1.2
        (if h : (greedySidon.aux 10).1.1.Nonempty then
          (greedySidon.aux 10).1.1.max' h + 1 else (greedySidon.aux 10).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 10).1.1.max' hNE = 97 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} : Finset ℕ) := h10s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h10s ▸ (by decide : (97 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h10s _ hB]
  exact go_step11 hB

private lemma aux_11_set : (greedySidon.aux 11).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} := by
  rw [aux_succ_set_eq, aux_10_set, aux_11_val]; decide

private lemma go_step12 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} hA 124).1 = 148 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 124 147 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 124: 1+124 = 123+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 124 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (124:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (124:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 125: 1+125 = 81+45
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 125 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (125:ℕ) = 45 ↔ False from by decide, show (1:ℕ) = 45 ↔ False from by decide, show (125:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 126: 1+126 = 123+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 126 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (126:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (126:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 127: 1+127 = 97+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 127 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (127:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (127:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 128: 4+128 = 66+66
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 128 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 66 ↔ False from by decide, show (128:ℕ) = 66 ↔ False from by decide, show (4:ℕ) = 66 ↔ False from by decide, show (128:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 129: 2+129 = 123+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 129 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 123 ↔ False from by decide, show (129:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (129:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 130: 1+130 = 123+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 130 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (130:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (130:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 131: 1+131 = 66+66
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 131 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (131:ℕ) = 66 ↔ False from by decide, show (1:ℕ) = 66 ↔ False from by decide, show (131:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 132: 4+132 = 123+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 132 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 123 ↔ False from by decide, show (132:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (132:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 133: 21+133 = 123+31
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 133 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 123 ↔ False from by decide, show (133:ℕ) = 31 ↔ False from by decide, show (21:ℕ) = 31 ↔ False from by decide, show (133:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 134: 2+134 = 123+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 134 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 123 ↔ False from by decide, show (134:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (134:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 135: 1+135 = 123+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 135 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (135:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (135:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 136: 8+136 = 123+21
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 136 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 123 ↔ False from by decide, show (136:ℕ) = 21 ↔ False from by decide, show (8:ℕ) = 21 ↔ False from by decide, show (136:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 137: 31+137 = 123+45
        right; intro hsidon
        have hcontra := hsidon 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 137 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (31:ℕ) = 123 ↔ False from by decide, show (137:ℕ) = 45 ↔ False from by decide, show (31:ℕ) = 45 ↔ False from by decide, show (137:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 138: 4+138 = 97+45
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 138 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 97 ↔ False from by decide, show (138:ℕ) = 45 ↔ False from by decide, show (4:ℕ) = 45 ↔ False from by decide, show (138:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 139: 8+139 = 81+66
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 139 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 81 ↔ False from by decide, show (139:ℕ) = 66 ↔ False from by decide, show (8:ℕ) = 66 ↔ False from by decide, show (139:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 140: 2+140 = 97+45
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 140 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (140:ℕ) = 45 ↔ False from by decide, show (2:ℕ) = 45 ↔ False from by decide, show (140:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 141: 1+141 = 97+45
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 141 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (141:ℕ) = 45 ↔ False from by decide, show (1:ℕ) = 45 ↔ False from by decide, show (141:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 142: 2+142 = 123+21
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 142 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 123 ↔ False from by decide, show (142:ℕ) = 21 ↔ False from by decide, show (2:ℕ) = 21 ↔ False from by decide, show (142:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 143: 1+143 = 123+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 143 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (143:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (143:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 144: 45+144 = 123+66
        right; intro hsidon
        have hcontra := hsidon 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 144 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (45:ℕ) = 123 ↔ False from by decide, show (144:ℕ) = 66 ↔ False from by decide, show (45:ℕ) = 66 ↔ False from by decide, show (144:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 145: 2+145 = 81+66
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 145 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 81 ↔ False from by decide, show (145:ℕ) = 66 ↔ False from by decide, show (2:ℕ) = 66 ↔ False from by decide, show (145:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 146: 1+146 = 81+66
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 146 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (146:ℕ) = 66 ↔ False from by decide, show (1:ℕ) = 66 ↔ False from by decide, show (146:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 147: 21+147 = 123+45
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 147 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 123 ↔ False from by decide, show (147:ℕ) = 45 ↔ False from by decide, show (21:ℕ) = 45 ↔ False from by decide, show (147:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_12_val : (greedySidon.aux 12).2 = 148 := by
  have h11s := aux_11_set
  have hNE : (greedySidon.aux 11).1.1.Nonempty :=
    h11s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 12).2 =
      (greedySidon.go (greedySidon.aux 11).1.1 (greedySidon.aux 11).1.2
        (if h : (greedySidon.aux 11).1.1.Nonempty then
          (greedySidon.aux 11).1.1.max' h + 1 else (greedySidon.aux 11).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 11).1.1.max' hNE = 123 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} : Finset ℕ) := h11s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h11s ▸ (by decide : (123 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h11s _ hB]
  exact go_step12 hB

private lemma aux_12_set : (greedySidon.aux 12).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} := by
  rw [aux_succ_set_eq, aux_11_set, aux_12_val]; decide

private lemma go_step13 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} hA 149).1 = 182 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 149 181 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 149: 1+149 = 148+2
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 149 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (149:ℕ) = 2 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide, show (149:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 150: 2+150 = 148+4
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 150 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 148 ↔ False from by decide, show (150:ℕ) = 4 ↔ False from by decide, show (2:ℕ) = 4 ↔ False from by decide, show (150:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 151: 1+151 = 148+4
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 151 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (151:ℕ) = 4 ↔ False from by decide, show (1:ℕ) = 4 ↔ False from by decide, show (151:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 152: 2+152 = 123+31
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 152 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 123 ↔ False from by decide, show (152:ℕ) = 31 ↔ False from by decide, show (2:ℕ) = 31 ↔ False from by decide, show (152:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 153: 1+153 = 123+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 153 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (153:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (153:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 154: 2+154 = 148+8
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 154 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 148 ↔ False from by decide, show (154:ℕ) = 8 ↔ False from by decide, show (2:ℕ) = 8 ↔ False from by decide, show (154:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 155: 1+155 = 148+8
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 155 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (155:ℕ) = 8 ↔ False from by decide, show (1:ℕ) = 8 ↔ False from by decide, show (155:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 156: 13+156 = 148+21
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 156 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 148 ↔ False from by decide, show (156:ℕ) = 21 ↔ False from by decide, show (13:ℕ) = 21 ↔ False from by decide, show (156:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 157: 4+157 = 148+13
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 157 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 148 ↔ False from by decide, show (157:ℕ) = 13 ↔ False from by decide, show (4:ℕ) = 13 ↔ False from by decide, show (157:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 158: 4+158 = 81+81
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 158 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 81 ↔ False from by decide, show (158:ℕ) = 81 ↔ False from by decide, show (4:ℕ) = 81 ↔ False from by decide, show (158:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 159: 2+159 = 148+13
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 159 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 148 ↔ False from by decide, show (159:ℕ) = 13 ↔ False from by decide, show (2:ℕ) = 13 ↔ False from by decide, show (159:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 160: 1+160 = 148+13
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 160 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (160:ℕ) = 13 ↔ False from by decide, show (1:ℕ) = 13 ↔ False from by decide, show (160:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 161: 1+161 = 81+81
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 161 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (161:ℕ) = 81 ↔ False from by decide, show (1:ℕ) = 81 ↔ False from by decide, show (161:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 162: 1+162 = 97+66
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 162 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (162:ℕ) = 66 ↔ False from by decide, show (1:ℕ) = 66 ↔ False from by decide, show (162:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 163: 31+163 = 97+97
        right; intro hsidon
        have hcontra := hsidon 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 163 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (31:ℕ) = 97 ↔ False from by decide, show (163:ℕ) = 97 ↔ False from by decide, show (31:ℕ) = 97 ↔ False from by decide, show (163:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 164: 4+164 = 123+45
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 164 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 123 ↔ False from by decide, show (164:ℕ) = 45 ↔ False from by decide, show (4:ℕ) = 45 ↔ False from by decide, show (164:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 165: 4+165 = 148+21
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 165 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 148 ↔ False from by decide, show (165:ℕ) = 21 ↔ False from by decide, show (4:ℕ) = 21 ↔ False from by decide, show (165:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 166: 2+166 = 123+45
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 166 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 123 ↔ False from by decide, show (166:ℕ) = 45 ↔ False from by decide, show (2:ℕ) = 45 ↔ False from by decide, show (166:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 167: 1+167 = 123+45
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 167 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 123 ↔ False from by decide, show (167:ℕ) = 45 ↔ False from by decide, show (1:ℕ) = 45 ↔ False from by decide, show (167:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 168: 1+168 = 148+21
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 168 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (168:ℕ) = 21 ↔ False from by decide, show (1:ℕ) = 21 ↔ False from by decide, show (168:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 169: 45+169 = 148+66
        right; intro hsidon
        have hcontra := hsidon 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 169 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (45:ℕ) = 148 ↔ False from by decide, show (169:ℕ) = 66 ↔ False from by decide, show (45:ℕ) = 66 ↔ False from by decide, show (169:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 170: 8+170 = 97+81
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 170 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 97 ↔ False from by decide, show (170:ℕ) = 81 ↔ False from by decide, show (8:ℕ) = 81 ↔ False from by decide, show (170:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 171: 8+171 = 148+31
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 171 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 148 ↔ False from by decide, show (171:ℕ) = 31 ↔ False from by decide, show (8:ℕ) = 31 ↔ False from by decide, show (171:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 172: 21+172 = 148+45
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 172 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 148 ↔ False from by decide, show (172:ℕ) = 45 ↔ False from by decide, show (21:ℕ) = 45 ↔ False from by decide, show (172:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 173: 21+173 = 97+97
        right; intro hsidon
        have hcontra := hsidon 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 173 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (21:ℕ) = 97 ↔ False from by decide, show (173:ℕ) = 97 ↔ False from by decide, show (21:ℕ) = 97 ↔ False from by decide, show (173:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 174: 4+174 = 97+81
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 174 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 97 ↔ False from by decide, show (174:ℕ) = 81 ↔ False from by decide, show (4:ℕ) = 81 ↔ False from by decide, show (174:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 175: 4+175 = 148+31
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 175 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 148 ↔ False from by decide, show (175:ℕ) = 31 ↔ False from by decide, show (4:ℕ) = 31 ↔ False from by decide, show (175:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 176: 2+176 = 97+81
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 176 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 97 ↔ False from by decide, show (176:ℕ) = 81 ↔ False from by decide, show (2:ℕ) = 81 ↔ False from by decide, show (176:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 177: 1+177 = 97+81
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 177 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (177:ℕ) = 81 ↔ False from by decide, show (1:ℕ) = 81 ↔ False from by decide, show (177:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 178: 1+178 = 148+31
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 178 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 148 ↔ False from by decide, show (178:ℕ) = 31 ↔ False from by decide, show (1:ℕ) = 31 ↔ False from by decide, show (178:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 179: 66+179 = 148+97
        right; intro hsidon
        have hcontra := hsidon 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 179 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (66:ℕ) = 148 ↔ False from by decide, show (179:ℕ) = 97 ↔ False from by decide, show (66:ℕ) = 97 ↔ False from by decide, show (179:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 180: 13+180 = 148+45
        right; intro hsidon
        have hcontra := hsidon 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 180 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (13:ℕ) = 148 ↔ False from by decide, show (180:ℕ) = 45 ↔ False from by decide, show (13:ℕ) = 45 ↔ False from by decide, show (180:ℕ) = 148 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 181: 8+181 = 123+66
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 181 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 123 ↔ False from by decide, show (181:ℕ) = 66 ↔ False from by decide, show (8:ℕ) = 66 ↔ False from by decide, show (181:ℕ) = 123 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_13_val : (greedySidon.aux 13).2 = 182 := by
  have h12s := aux_12_set
  have hNE : (greedySidon.aux 12).1.1.Nonempty :=
    h12s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 13).2 =
      (greedySidon.go (greedySidon.aux 12).1.1 (greedySidon.aux 12).1.2
        (if h : (greedySidon.aux 12).1.1.Nonempty then
          (greedySidon.aux 12).1.1.max' h + 1 else (greedySidon.aux 12).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 12).1.1.max' hNE = 148 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} : Finset ℕ) := h12s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h12s ▸ (by decide : (148 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h12s _ hB]
  exact go_step13 hB

private lemma aux_13_set : (greedySidon.aux 13).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} := by
  rw [aux_succ_set_eq, aux_12_set, aux_13_val]; decide

private lemma go_step14 (hA : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} : Finset ℕ) : Set ℕ)) :
    (greedySidon.go {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} hA 183).1 = 204 :=
  go_eq_val hA (by decide) (by decide) (by decide) (by decide)
    (fun k hk1 hk2 => by
      have hkrange : k ∈ Finset.Icc 183 203 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      fin_cases hkrange
      · -- k = 183: 1+183 = 2+182
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 183 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 2 ↔ False from by decide, show (183:ℕ) = 182 ↔ False from by decide, show (1:ℕ) = 182 ↔ False from by decide, show (183:ℕ) = 2 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 184: 2+184 = 4+182
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 184 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 4 ↔ False from by decide, show (184:ℕ) = 182 ↔ False from by decide, show (2:ℕ) = 182 ↔ False from by decide, show (184:ℕ) = 4 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 185: 1+185 = 4+182
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 185 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 4 ↔ False from by decide, show (185:ℕ) = 182 ↔ False from by decide, show (1:ℕ) = 182 ↔ False from by decide, show (185:ℕ) = 4 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 186: 4+186 = 8+182
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 186 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 8 ↔ False from by decide, show (186:ℕ) = 182 ↔ False from by decide, show (4:ℕ) = 182 ↔ False from by decide, show (186:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 187: 2+187 = 66+123
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 187 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 66 ↔ False from by decide, show (187:ℕ) = 123 ↔ False from by decide, show (2:ℕ) = 123 ↔ False from by decide, show (187:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 188: 1+188 = 66+123
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 188 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 66 ↔ False from by decide, show (188:ℕ) = 123 ↔ False from by decide, show (1:ℕ) = 123 ↔ False from by decide, show (188:ℕ) = 66 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 189: 1+189 = 8+182
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 189 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 8 ↔ False from by decide, show (189:ℕ) = 182 ↔ False from by decide, show (1:ℕ) = 182 ↔ False from by decide, show (189:ℕ) = 8 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 190: 4+190 = 97+97
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 190 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 97 ↔ False from by decide, show (190:ℕ) = 97 ↔ False from by decide, show (4:ℕ) = 97 ↔ False from by decide, show (190:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 191: 2+191 = 45+148
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 191 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 45 ↔ False from by decide, show (191:ℕ) = 148 ↔ False from by decide, show (2:ℕ) = 148 ↔ False from by decide, show (191:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 192: 1+192 = 45+148
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 45 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 192 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 45 ↔ False from by decide, show (192:ℕ) = 148 ↔ False from by decide, show (1:ℕ) = 148 ↔ False from by decide, show (192:ℕ) = 45 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 193: 1+193 = 97+97
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 193 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 97 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 97 ↔ False from by decide, show (193:ℕ) = 97 ↔ False from by decide, show (1:ℕ) = 97 ↔ False from by decide, show (193:ℕ) = 97 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 194: 1+194 = 13+182
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 13 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 194 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 13 ↔ False from by decide, show (194:ℕ) = 182 ↔ False from by decide, show (1:ℕ) = 182 ↔ False from by decide, show (194:ℕ) = 13 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 195: 8+195 = 21+182
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 195 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 21 ↔ False from by decide, show (195:ℕ) = 182 ↔ False from by decide, show (8:ℕ) = 182 ↔ False from by decide, show (195:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 196: 8+196 = 81+123
        right; intro hsidon
        have hcontra := hsidon 8 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 196 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (8:ℕ) = 81 ↔ False from by decide, show (196:ℕ) = 123 ↔ False from by decide, show (8:ℕ) = 123 ↔ False from by decide, show (196:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 197: 66+197 = 81+182
        right; intro hsidon
        have hcontra := hsidon 66 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 197 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (66:ℕ) = 81 ↔ False from by decide, show (197:ℕ) = 182 ↔ False from by decide, show (66:ℕ) = 182 ↔ False from by decide, show (197:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 198: 31+198 = 81+148
        right; intro hsidon
        have hcontra := hsidon 31 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 198 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 148 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (31:ℕ) = 81 ↔ False from by decide, show (198:ℕ) = 148 ↔ False from by decide, show (31:ℕ) = 148 ↔ False from by decide, show (198:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 199: 4+199 = 21+182
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 199 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 21 ↔ False from by decide, show (199:ℕ) = 182 ↔ False from by decide, show (4:ℕ) = 182 ↔ False from by decide, show (199:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 200: 4+200 = 81+123
        right; intro hsidon
        have hcontra := hsidon 4 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 200 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (4:ℕ) = 81 ↔ False from by decide, show (200:ℕ) = 123 ↔ False from by decide, show (4:ℕ) = 123 ↔ False from by decide, show (200:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 201: 2+201 = 21+182
        right; intro hsidon
        have hcontra := hsidon 2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 201 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (2:ℕ) = 21 ↔ False from by decide, show (201:ℕ) = 182 ↔ False from by decide, show (2:ℕ) = 182 ↔ False from by decide, show (201:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 202: 1+202 = 21+182
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 21 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 202 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 182 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 21 ↔ False from by decide, show (202:ℕ) = 182 ↔ False from by decide, show (1:ℕ) = 182 ↔ False from by decide, show (202:ℕ) = 21 ↔ False from by decide, false_and, and_false, or_self] at hcontra
      · -- k = 203: 1+203 = 81+123
        right; intro hsidon
        have hcontra := hsidon 1 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 81 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) 203 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))) 123 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl (by decide)))) (by norm_num)
        simp only [show (1:ℕ) = 81 ↔ False from by decide, show (203:ℕ) = 123 ↔ False from by decide, show (1:ℕ) = 123 ↔ False from by decide, show (203:ℕ) = 81 ↔ False from by decide, false_and, and_false, or_self] at hcontra
    )

private lemma aux_14_val : (greedySidon.aux 14).2 = 204 := by
  have h13s := aux_13_set
  have hNE : (greedySidon.aux 13).1.1.Nonempty :=
    h13s ▸ (by decide : ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} : Finset ℕ).Nonempty)
  rw [show (greedySidon.aux 14).2 =
      (greedySidon.go (greedySidon.aux 13).1.1 (greedySidon.aux 13).1.2
        (if h : (greedySidon.aux 13).1.1.Nonempty then
          (greedySidon.aux 13).1.1.max' h + 1 else (greedySidon.aux 13).2)).1 from rfl,
    dif_pos hNE]
  have hmax : (greedySidon.aux 13).1.1.max' hNE = 182 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have hmem : y ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} : Finset ℕ) := h13s ▸ hy
      simp [Finset.mem_insert, Finset.mem_singleton] at hmem; omega
    · apply Finset.le_max'
      exact h13s ▸ (by decide : (182 : ℕ) ∈ ({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} : Finset ℕ))
  rw [hmax]
  have hB : IsSidon (({1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182} : Finset ℕ) : Set ℕ) := by decide
  rw [go_set_eq h13s _ hB]
  exact go_step14 hB

private lemma aux_14_set : (greedySidon.aux 14).1.1 = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182, 204} := by
  rw [aux_succ_set_eq, aux_13_set, aux_14_val]; decide


private lemma greedySidon_13 : greedySidon 13 = 182 := aux_13_val

private lemma greedySidon_14 : greedySidon 14 = 204 := aux_14_val

@[category research formally solved using formal_conjectures at "https://erdosproblems.com/340", AMS 11]
theorem erdos_340.variants._22_mem_sub :
    22 ∈ Set.range greedySidon - Set.range greedySidon := by
  refine ⟨204, 182, ⟨14, greedySidon_14⟩, ⟨13, greedySidon_13⟩, ?_⟩
  norm_num

end Erdos340
