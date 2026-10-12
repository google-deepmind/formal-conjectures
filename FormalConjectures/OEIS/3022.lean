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
# Optimal Golomb rulers (OEIS A003022)

A Golomb ruler is a finite set of integer marks for which all positive pairwise distances
determined by distinct unordered pairs of marks are different. Its length is the distance between
its first and last marks. OEIS A003022 records the smallest possible length of a Golomb ruler with
a prescribed number of marks.

Equivalently, after translating the first mark to zero, the marks form a Sidon subset of an
interval from zero to the ruler's length. We extend the official offset-two sequence by setting
the values at zero and one marks to zero.

*References:*
- [OEIS A003022](https://oeis.org/A003022)
-/

@[expose] public section

namespace OeisA3022

/--
The smallest length of a Golomb ruler with $n$ marks, extended by $a(0)=a(1)=0$.

The condition under the infimum says that the interval $\{0,\ldots,L\}$ contains a Sidon subset
with at least $n$ elements.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {L : ℕ | n ≤ Finset.maxSidonSubsetCard (Finset.Icc 0 L)}

/-- Identify `a n` once a feasible length and the failure of every smaller length are known. -/
@[category API, AMS 5 11]
lemma a_eq_of_minimal (n L : ℕ)
    (hL : n ≤ Finset.maxSidonSubsetCard (Finset.Icc 0 L))
    (hmin : ∀ m < L, ¬ n ≤ Finset.maxSidonSubsetCard (Finset.Icc 0 m)) :
    a n = L := by
  unfold a
  apply le_antisymm
  · exact Nat.sInf_le hL
  · apply le_csInf ⟨L, hL⟩
    intro m hm
    by_contra h
    exact hmin m (by omega) hm

/-- Feasibility can be checked using subsets with exactly the prescribed number of marks. -/
@[category API, AMS 5 11]
private lemma le_max_sidon_subset_card_iff (n : ℕ) (hn : 0 < n) (A : Finset ℕ) :
    n ≤ A.maxSidonSubsetCard ↔
      ∃ B ⊆ A, B.card = n ∧ IsSidon (B : Set ℕ) := by
  rw [Finset.maxSidonSubsetCard, Finset.le_sup_iff hn]
  constructor
  · rintro ⟨B, hB, hnB⟩
    obtain ⟨C, hCB, hC⟩ := Finset.exists_subset_card_eq hnB
    obtain ⟨hBA, hB⟩ := Finset.mem_filter.mp hB
    exact ⟨C, hCB.trans (Finset.mem_powerset.mp hBA), hC,
      Set.IsSidon.subset hB (Finset.coe_subset.mpr hCB)⟩
  · rintro ⟨B, hBA, rfl, hB⟩
    exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBA, hB⟩, le_rfl⟩

/-- The sorted marks of a bounded ruler occur in the finite list search. -/
@[category API, AMS 5 11]
private lemma sort_sublist_range {L : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range L) :
    List.Sublist (C.sort (· ≤ ·)) (List.range L) := by
  rw [← Finset.sort_range]
  apply List.sublist_of_subperm_of_pairwise (r := (· ≤ ·))
  · apply List.subperm_of_subset (C.sort_nodup (· ≤ ·))
    intro x hx
    exact (Finset.mem_sort _).mpr (hC ((Finset.mem_sort _).mp hx))
  · exact C.pairwise_sort (· ≤ ·)
  · exact (Finset.range L).pairwise_sort (· ≤ ·)

/-- Check the Sidon pair-sum condition using finite Boolean loops. -/
private def sidonCheck (l : List ℕ) : Bool :=
  l.all fun a ↦ l.all fun b ↦ l.all fun c ↦ l.all fun d ↦
    decide (a + c = b + d → (a = b ∧ c = d) ∨ (a = d ∧ c = b))

/-- The Boolean check agrees with the Sidon condition on the list's finite set. -/
@[category API, AMS 5 11]
private lemma sidon_check_eq_true_iff (l : List ℕ) :
    sidonCheck l = true ↔ IsSidon (l.toFinset : Set ℕ) := by
  simp only [sidonCheck, List.all_eq_true, decide_eq_true_eq, IsSidon,
    Finset.mem_coe, List.mem_toFinset]

/-- A negative finite Boolean search excludes every ruler with the prescribed marks. -/
@[category API, AMS 5 11]
private lemma sidon_exclusion_of_check (n L : ℕ)
    (hcheck : ((List.range L).sublistsLen n).all (fun l ↦ !sidonCheck l) = true) :
    ∀ l ∈ (List.range L).sublistsLen n, ¬ IsSidon (l.toFinset : Set ℕ) := by
  intro l hl hSidon
  have hfalse := List.all_eq_true.mp hcheck l hl
  have htrue := (sidon_check_eq_true_iff l).mpr hSidon
  simp [htrue] at hfalse

/-- A witness at length `L` and exclusion below `L` determine the optimum. -/
@[category API, AMS 5 11]
lemma a_eq_of_witness (n L : ℕ) (hn : 0 < n) (B : Finset ℕ)
    (hB : B ⊆ Finset.Icc 0 L) (hcard : B.card = n) (hSidon : IsSidon (B : Set ℕ))
    (hno : ∀ l ∈ (List.range L).sublistsLen n, ¬ IsSidon (l.toFinset : Set ℕ)) :
    a n = L := by
  apply a_eq_of_minimal
  · exact (le_max_sidon_subset_card_iff n hn _).mpr ⟨B, hB, hcard, hSidon⟩
  · intro m hm h
    obtain ⟨C, hC, hcard, hSidon⟩ := (le_max_sidon_subset_card_iff n hn _).mp h
    have hCR : C ⊆ Finset.range L := by
      intro x hx
      have hxm := (Finset.mem_Icc.mp (hC hx)).2
      exact Finset.mem_range.mpr (by omega)
    apply hno (C.sort (· ≤ ·)) (List.mem_sublistsLen.mpr
      ⟨sort_sublist_range hCR, by simpa using hcard⟩)
    simpa only [Finset.sort_toFinset] using hSidon

@[category test, AMS 5 11]
theorem a_0 : a 0 = 0 := by
  apply a_eq_of_minimal
  · decide
  · intro m hm
    omega

@[category test, AMS 5 11]
theorem a_1 : a 1 = 0 := by
  apply a_eq_of_minimal
  · decide
  · intro m hm
    omega

@[category test, AMS 5 11]
theorem a_2 : a 2 = 1 := by
  apply a_eq_of_minimal
  · decide
  · intro m hm
    interval_cases m
    decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 3 := by
  apply a_eq_of_minimal
  · decide
  · intro m hm
    interval_cases m <;> decide

set_option maxRecDepth 100000 in
@[category test, AMS 5 11]
theorem a_4 : a 4 = 6 := by
  apply a_eq_of_minimal
  · decide
  · intro m hm
    interval_cases m <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
@[category test, AMS 5 11]
theorem a_5 : a 5 = 11 := by
  apply a_eq_of_witness 5 11 (by decide) {0, 1, 4, 9, 11}
  · decide
  · decide
  · decide
  · exact sidon_exclusion_of_check 5 11 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem a_6 : a 6 = 17 := by
  apply a_eq_of_witness 6 17 (by decide) {0, 1, 4, 10, 12, 17}
  · decide
  · decide
  · decide
  · exact sidon_exclusion_of_check 6 17 (by decide +kernel)

/--
OEIS A003022: “Length of shortest (or optimal) Golomb ruler with n marks.”

What is the exact length of an optimal Golomb ruler with $29$ marks? The OEIS table currently
records exact values through $28$ marks.
-/
@[category research open, AMS 5 11]
theorem a_29 : a 29 = answer(sorry) := by
  sorry

end OeisA3022
