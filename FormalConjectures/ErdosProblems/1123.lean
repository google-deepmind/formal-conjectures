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

import FormalConjecturesUtil

/-!
# Erdős Problem 1123

*References:*
- [erdosproblems.com/1123](https://www.erdosproblems.com/1123)
- [Er81b] Erdős, P., *My Scottish Book 'Problems'*. The Scottish Book (1981), 27–35.
- [JuKr84] Just, W. and Krawczyk, A., *On certain Boolean algebras ${\scr P}(\omega)/I$*.
  Trans. Amer. Math. Soc. (1984), 411–429.
- [Fa00] Farah, I., *Analytic quotients: theory of liftings for quotients over analytic ideals
  on the integers*. Mem. Amer. Math. Soc. (2000).
-/

open Filter Finset Set
open scoped BigOperators BooleanRingOfBooleanAlgebra Cardinal symmDiff Topology

namespace Erdos1123

/- Density zero is an ideal. -/

@[category API, AMS 3 6]
lemma partialDensity_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ S.partialDensity univ n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

@[category API, AMS 3 6]
lemma hasDensity_zero_of_subset {S T : Set ℕ} (hST : S ⊆ T) (hT : T.HasDensity 0) :
    S.HasDensity 0 := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
    (fun n => partialDensity_nonneg S n) fun n => ?_
  simp only [partialDensity, inter_univ]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hfin : (T ∩ Set.Iio n).Finite := (finite_Iio n).subset inter_subset_right
  exact Nat.cast_le.mpr (ncard_le_ncard (inter_subset_inter_left _ hST) hfin)

@[category API, AMS 3 6]
lemma hasDensity_zero_union {S T : Set ℕ} (hS : S.HasDensity 0) (hT : T.HasDensity 0) :
    (S ∪ T).HasDensity 0 := by
  have hsum :
      Tendsto (fun n => S.partialDensity univ n + T.partialDensity univ n) atTop (𝓝 0) := by
    simpa using hS.add hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => partialDensity_nonneg (S ∪ T) n) fun n => ?_
  simp only [partialDensity, inter_univ]
  rw [union_inter_distrib_right]
  have hle : (((S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n)).ncard : ℝ) ≤
      ((S ∩ Set.Iio n).ncard : ℝ) + (T ∩ Set.Iio n).ncard := by
    exact_mod_cast ncard_union_le (S ∩ Set.Iio n) (T ∩ Set.Iio n)
  calc
    ((((S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n)).ncard : ℝ) / (univ ∩ Set.Iio n).ncard)
      ≤ ((S ∩ Set.Iio n).ncard + (T ∩ Set.Iio n).ncard : ℝ) / (univ ∩ Set.Iio n).ncard :=
        div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)
    _ = (S ∩ Set.Iio n).ncard / (univ ∩ Set.Iio n).ncard +
        (T ∩ Set.Iio n).ncard / (univ ∩ Set.Iio n).ncard := add_div _ _ _

open Classical in
@[category API, AMS 3 6]
lemma hasLogDensity_empty : (∅ : Set ℕ).HasLogDensity 0 := by
  simp [HasLogDensity]

open Classical in
@[category API, AMS 3 6]
lemma logDensityPartial_eq (A : Set ℕ) (n : ℕ) :
    (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / Real.log n) =
      (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹) / Real.log n := by
  simp_rw [div_eq_mul_inv, sum_mul]

open Classical in
@[category API, AMS 3 6]
lemma logDensity_sum_inv_mono {S T : Set ℕ} (hST : S ⊆ T) (n : ℕ) :
    (∑ k ≤ n with k ∈ S, (k : ℝ)⁻¹) ≤ ∑ k ≤ n with k ∈ T, (k : ℝ)⁻¹ := by
  refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
  intro k hk
  simp only [mem_filter] at hk ⊢
  exact ⟨hk.1, hST hk.2⟩

open Classical in
@[category API, AMS 3 6]
lemma hasLogDensity_zero_of_subset {S T : Set ℕ} (hST : S ⊆ T) (hT : T.HasLogDensity 0) :
    S.HasLogDensity 0 := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    rw [logDensityPartial_eq]
    exact div_nonneg (sum_nonneg fun k _ => inv_nonneg.2 (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by lia)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp_rw [logDensityPartial_eq]
    exact div_le_div_of_nonneg_right (logDensity_sum_inv_mono hST n)
      (Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by lia)))

open Classical in
@[category API, AMS 3 6]
lemma hasLogDensity_zero_union {S T : Set ℕ} (hS : S.HasLogDensity 0) (hT : T.HasLogDensity 0) :
    (S ∪ T).HasLogDensity 0 := by
  have hsum :
      Tendsto (fun n =>
        (∑ k ≤ n with k ∈ S, (k : ℝ)⁻¹ / Real.log n) +
          ∑ k ≤ n with k ∈ T, (k : ℝ)⁻¹ / Real.log n) atTop (𝓝 0) := by
    simpa using hS.add hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact sum_nonneg fun _ _ =>
      div_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by lia)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by lia))
    let s := (Finset.Iic n).filter (· ∈ S)
    let t := (Finset.Iic n).filter (· ∈ T)
    let u := (Finset.Iic n).filter (· ∈ S ∪ T)
    have hsubset : u ⊆ s ∪ t := by
      intro k hk
      simp only [s, t, u, Finset.mem_union, mem_filter, Set.mem_union] at hk ⊢
      exact hk.2.elim (fun hSmem => Or.inl ⟨hk.1, hSmem⟩) fun hTmem => Or.inr ⟨hk.1, hTmem⟩
    have hterm : ∀ k : ℕ, 0 ≤ (k : ℝ)⁻¹ / Real.log n := fun k =>
      div_nonneg (inv_nonneg.2 (Nat.cast_nonneg k)) hlog
    have hle_subset : ∑ k ∈ u, (k : ℝ)⁻¹ / Real.log n ≤
        ∑ k ∈ s ∪ t, (k : ℝ)⁻¹ / Real.log n :=
      sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ => hterm k
    have hEq : ∑ k ∈ s ∪ t, (k : ℝ)⁻¹ / Real.log n + ∑ k ∈ s ∩ t, (k : ℝ)⁻¹ / Real.log n =
        ∑ k ∈ s, (k : ℝ)⁻¹ / Real.log n + ∑ k ∈ t, (k : ℝ)⁻¹ / Real.log n :=
      sum_union_inter (s₁ := s) (s₂ := t)
    have hinter : 0 ≤ ∑ k ∈ s ∩ t, (k : ℝ)⁻¹ / Real.log n :=
      sum_nonneg fun k _ => hterm k
    have hle_union : ∑ k ∈ s ∪ t, (k : ℝ)⁻¹ / Real.log n ≤
        ∑ k ∈ s, (k : ℝ)⁻¹ / Real.log n + ∑ k ∈ t, (k : ℝ)⁻¹ / Real.log n := by
      linarith
    simpa [s, t, u] using hle_subset.trans hle_union

/-- The ideal of sets of natural density zero. -/
def densityZeroIdeal : Ideal (Set ℕ) where
  carrier := {A | A.HasDensity 0}
  add_mem' hA hB :=
    hasDensity_zero_of_subset symmDiff_subset_union (hasDensity_zero_union hA hB)
  zero_mem' := HasDensity.empty
  smul_mem' _ _ hA := hasDensity_zero_of_subset (fun _ hx => hx.2) hA

/-- The ideal of sets of logarithmic density zero. -/
def logDensityZeroIdeal : Ideal (Set ℕ) where
  carrier := {A | A.HasLogDensity 0}
  add_mem' hA hB :=
    hasLogDensity_zero_of_subset symmDiff_subset_union (hasLogDensity_zero_union hA hB)
  zero_mem' := hasLogDensity_empty
  smul_mem' _ _ hA := hasLogDensity_zero_of_subset (fun _ hx => hx.2) hA

instance : BooleanRing (Set ℕ ⧸ densityZeroIdeal) where
  isIdempotentElem := by
    rintro ⟨A⟩
    exact congrArg _ (BooleanRing.mul_self A)

instance : BooleanRing (Set ℕ ⧸ logDensityZeroIdeal) where
  isIdempotentElem := by
    rintro ⟨A⟩
    exact congrArg _ (BooleanRing.mul_self A)

/--
The Boolean algebra $B_1$ of sets of naturals modulo density zero. Equivalence of sets is
symmetric difference of natural density zero, matching $\mathcal{P}(\omega)/\mathcal{Z}_0$
in [JuKr84] and [Fa00].
-/
abbrev B1 : Type := AsBoolAlg (Set ℕ ⧸ densityZeroIdeal)

/--
The Boolean algebra $B_2$ of sets of naturals modulo logarithmic density zero. Equivalence of
sets is symmetric difference of logarithmic density zero.
-/
abbrev B2 : Type := AsBoolAlg (Set ℕ ⧸ logDensityZeroIdeal)

-- The question is independent of ZFC (see the docstring), so the answer stays a placeholder.
set_option linter.style.category_answer false in
/--
Let $B_1$ be the Boolean algebra of sets of integers modulo sets of density $0$ (that is,
in which two sets are equivalent if and only if they differ by a set of density $0$) and let
$B_2$ be the Boolean algebra of sets modulo sets of logarithmic density $0$.

Prove that $B_1$ and $B_2$ are not isomorphic.

This is a question of Erdős and Ulam. The claim is **independent of ZFC**, so the headline
statement carries `answer(sorry)`: it is neither provable nor refutable from the usual axioms
of set theory.

Just and Krawczyk [JuKr84] proved that the algebras are isomorphic under the continuum
hypothesis (see `erdos_1123.variants.ch`). Farah [Fa00, Corollary 3.4.4] proved that they are
not isomorphic under the Open Coloring Axiom and Martin's Axiom.

Integers are formalised as $\mathbb{N}$, matching the standard presentation
$\mathcal{P}(\omega)/I$ in [JuKr84] and [Fa00]. Logarithmic density is defined on
$\mathbb{N}$ (see `Set.HasLogDensity`).
-/
@[category research solved, AMS 3 6]
theorem erdos_1123 : answer(sorry) ↔ ¬ Nonempty (B1 ≃o B2) := by
  sorry

/--
Just and Krawczyk [JuKr84] proved that if the continuum hypothesis holds, then the Boolean
algebras of sets modulo density zero and modulo logarithmic density zero are isomorphic.
-/
@[category research solved, AMS 3 6]
theorem erdos_1123.variants.ch (hCH : 𝔠 = ℵ_ 1) : Nonempty (B1 ≃o B2) := by
  sorry

end Erdos1123
