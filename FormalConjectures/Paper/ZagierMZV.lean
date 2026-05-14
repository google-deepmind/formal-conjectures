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
# Zagier's Conjecture on Multiple Zeta Values

*References:*
- [Za94] Zagier, Don. "Values of zeta functions and their applications."
  First European Congress of Mathematics Paris, July 6–10, 1992: Vol. II: Invited Lectures (Part 2). Basel: Birkhäuser Basel, 1994.
- [Co18] Combariza, Germán AG. "A few conjectures about the multiple zeta values."
  ACM Communications in Computer Algebra 52.1 (2018): 11-20.
- [Te02] T. Terasoma. Mixed Tate motives and multiple zeta values. Invent. Math., 149(2):339–369, 2002.
- [DG05] P. Deligne and A. Goncharov. Groupes fondamentaux motiviques de Tate mixte. Ann. Sci.
  Ecole Norm. Sup. (4), 38(1):1–56, 2005.
- [OEIS A000931](https://oeis.org/A000931)
-/

-- TODO(jgd) There are additional conjectures in Co18 which would be nice to formalize.

namespace ZagierMZV

open Finset BigOperators

/--
The multiple zeta value $\zeta(s_1, s_2, \ldots, s_k)$, defined as
$$\zeta(s_1, \ldots, s_k) = \sum_{n_1 > n_2 > \cdots > n_k > 0}
\frac{1}{n_1^{s_1} n_2^{s_2} \cdots n_k^{s_k}}.$$
The argument is a list of positive natural numbers. The value is well-defined (i.e. the series
converges) when the first entry is at least 2, but we define it for all inputs.
For the empty list, `multiZeta [] = 1` (the empty product convention).
-/
noncomputable def multiZeta : List ℕ → ℝ
  | [] => 1
  | s :: rest => ∑' n : ℕ, (1 / (n + 1 : ℝ) ^ s) * multiZeta.aux rest n
where
  /-- Auxiliary function for `multiZeta`: computes the inner sum
  $\sum_{n_2 > \cdots > n_k > 0, n_2 < \text{bound}} \frac{1}{n_2^{s_2} \cdots n_k^{s_k}}$. -/
  aux : List ℕ → ℕ → ℝ
  | [], _ => 1
  | s :: rest, bound => ∑ m ∈ Finset.range bound, (1 / (m + 1 : ℝ) ^ s) * aux rest m

/-- The *weight* of an MZV index $(s_1, \ldots, s_k)$ is $s_1 + \cdots + s_k$. -/
def weight (s : List ℕ) : ℕ := s.sum

/--
An MZV index is *admissible* if it is either empty or if the first entry is at least 2
and all entries are positive. The empty list convention ensures $\mathcal{Z}_0 = \mathbb{Q}$.
-/
def AdmissibleIndex : List ℕ → Prop
  | [] => True
  | s₁ :: rest => 1 < s₁ ∧ ∀ sᵢ ∈ rest, 0 < sᵢ

/-- The set of all MZV values of weight $n$. -/
def mzvSetOfWeight (n : ℕ) : Set ℝ :=
  multiZeta '' {s | AdmissibleIndex s ∧ weight s = n}

/-- The $\mathbb{Q}$-submodule of $\mathbb{R}$ spanned by all MZVs of weight $n$. -/
noncomputable def mzvSpanOfWeight (n : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (mzvSetOfWeight n)

/--
The conjectured Zagier dimension sequence $d_n$, defined by $d_0 = 1$, $d_1 = 0$, $d_2 = 1$,
and $d_n = d_{n-2} + d_{n-3}$ for $n \geq 3$.
-/
def zagierDim : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | (n + 3) => zagierDim (n + 1) + zagierDim n

/--
**Zagier's conjecture**

The $\mathbb{Q}$-dimension of the vector space spanned by all multiple zeta values
of weight $n$ equals $d_n$, where $d_n$ is the Zagier dimension sequence
satisfying $d_0 = 1$, $d_1 = 0$, $d_2 = 1$, and $d_n = d_{n-2} + d_{n-3}$ for $n \geq 3$.
-/
@[category research open, AMS 11]
theorem zagier_conjecture :
    answer(sorry) ↔ ∀ n : ℕ, Module.finrank ℚ (mzvSpanOfWeight n) = zagierDim n := by
  sorry

/--
**Upper bound** [Te02, DG05]

The dimension of the $\mathbb{Q}$-vector space of MZVs of weight $n$ is at most $d_n$.
-/
@[category research solved, AMS 11]
theorem zagier_upper_bound :
    ∀ n : ℕ, Module.finrank ℚ (mzvSpanOfWeight n) ≤ zagierDim n := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Tests
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/-- The first few values of $d_n$ are $1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, \ldots$ -/
@[category test, AMS 11]
theorem zagierDim_first_values :
    [zagierDim 0, zagierDim 1, zagierDim 2, zagierDim 3, zagierDim 4,
     zagierDim 5, zagierDim 6, zagierDim 7, zagierDim 8, zagierDim 9] =
    [1, 0, 1, 1, 1, 2, 2, 3, 4, 5] := by
  decide

/-- There is no admissible index of weight 1 (since $s_1 \geq 2$ is required). -/
@[category test, AMS 11]
theorem no_admissible_weight_one (s : List ℕ) (h : AdmissibleIndex s) : weight s ≠ 1 := by
  cases s with
  | nil =>
    unfold weight
    simp
  | cons s₁ rest =>
    unfold weight
    simp only [List.sum_cons]
    unfold AdmissibleIndex at h
    obtain ⟨h1, h2⟩ := h
    omega

/-- $\mathcal{Z}_0 = \mathbb{Q}$, so $\dim_\mathbb{Q}(\mathcal{Z}_0) = 1$. -/
@[category test, AMS 11]
theorem dim_mzv_weight_zero : Module.finrank ℚ (mzvSpanOfWeight 0) = 1 := by
  have h_set : mzvSetOfWeight 0 = {1} := by
    ext x
    simp only [mzvSetOfWeight, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, ⟨h_adm, hw⟩, rfl⟩
      cases s with
      | nil =>
        rfl
      | cons s₁ rest =>
        unfold weight at hw
        simp only [List.sum_cons] at hw
        unfold AdmissibleIndex at h_adm
        obtain ⟨h1, h2⟩ := h_adm
        omega
    · rintro rfl
      refine ⟨[], ⟨by simp [AdmissibleIndex], by rfl⟩, by rfl⟩
  rw [mzvSpanOfWeight, h_set]
  exact finrank_span_singleton (by norm_num)

/-- $\mathcal{Z}_1 = \emptyset$, so $\dim_\mathbb{Q}(\mathcal{Z}_1) = 0$. -/
@[category test, AMS 11]
theorem dim_mzv_weight_one : Module.finrank ℚ (mzvSpanOfWeight 1) = 0 := by
  have h_set : mzvSetOfWeight 1 = ∅ := by
    ext x
    simp only [mzvSetOfWeight, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨s, ⟨h_adm, hw⟩, rfl⟩
      exact no_admissible_weight_one s h_adm hw
    · rintro h
      exact h.elim
  rw [mzvSpanOfWeight, h_set, Submodule.span_empty, finrank_bot]

@[category test, AMS 11]
theorem multiZeta_empty : multiZeta [] = 1 := by
  simp [multiZeta]

/-- Euler's identity: $\zeta(2) = \pi^2/6$. -/
@[category test, AMS 11]
theorem multiZeta_two : multiZeta [2] = Real.pi ^ 2 / 6 := by
  have h1 : multiZeta [2] = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2 := by
    unfold multiZeta
    simp only [multiZeta.aux, mul_one]
  rw [h1]
  have h2 := hasSum_zeta_two
  have h3 : HasSum (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    have h4 : (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) = (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
      ext n
      push_cast
      rfl
    rw [← h4]
    have := (hasSum_nat_add_iff' 1).mpr h2
    have h_eval : Real.pi ^ 2 / 6 - ∑ i ∈ range 1, 1 / (i : ℝ) ^ 2 = Real.pi ^ 2 / 6 := by
      simp only [sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero]
    rwa [h_eval] at this
  exact h3.tsum_eq

/-- Euler's identity for $\zeta(4) = \pi^4/90$. -/
@[category test, AMS 11]
theorem multiZeta_four : multiZeta [4] = Real.pi ^ 4 / 90 := by
  have h1 : multiZeta [4] = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 4 := by
    unfold multiZeta
    simp only [multiZeta.aux, mul_one]
  rw [h1]
  have h2 := hasSum_zeta_four
  have h3 : HasSum (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 4) (Real.pi ^ 4 / 90) := by
    have h4 : (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 4) = (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 4) := by
      ext n
      push_cast
      rfl
    rw [← h4]
    have := (hasSum_nat_add_iff' 1).mpr h2
    have h_four : 4 ≠ 0 := by decide
    have h_eval : Real.pi ^ 4 / 90 - ∑ i ∈ range 1, 1 / (i : ℝ) ^ 4 = Real.pi ^ 4 / 90 := by
      simp only [sum_range_one, Nat.cast_zero, zero_pow h_four, div_zero, sub_zero]
    rwa [h_eval] at this
  exact h3.tsum_eq

end ZagierMZV
