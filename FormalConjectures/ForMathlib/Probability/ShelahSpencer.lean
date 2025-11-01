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

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
/-!
# Probability utilities for random graph statements

This file collects probability theory prerequisites that will be used when studying
finite random graphs such as `G(n, p)`, particularly `G(n, n^α)`.
The key lemma states that for each `n`, the measure on `G(n, n^α)` defined by cumulating a graph's
edge and non-edge probabilities (see `def graphProbabilityProduct `) is a probability measure.
-/


namespace ShelahSpencer
open MeasureTheory
open scoped BigOperators

instance MeasurableSpace (n : ℕ): MeasurableSpace (SimpleGraph (Fin n)) :=
{
    MeasurableSet' := fun _ => True
    measurableSet_empty := trivial
    measurableSet_compl:= by exact fun s a ↦ a
    measurableSet_iUnion:= fun _ _ => trivial
}


/-- Computes the product over all unordered pairs of distinct vertices:
    - For non-adjacent pairs {x,y}: multiply by (1 - p)
    - For adjacent pairs {x,y}: multiply by p

    This represents the probability density of observing graph G in the Erdős-Rényi
    random graph model G(n,p), where each edge appears independently with probability p.

    We iterate over ordered pairs (x,y) with x < y to ensure each unordered pair
    is counted exactly once, avoiding the double-counting issue.
-/
def graphProbabilityProduct {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) : ℝ :=
  (Finset.univ.product Finset.univ).filter (fun (x, y) => x < y) |>.prod fun (x, y) =>
    if G.Adj x y then p else (1 - p)

/-- The measure function for G(n,α) random graphs. -/
noncomputable def measureOf (n : ℕ) (α : ℝ) (S : Set (SimpleGraph (Fin n))) : ENNReal :=
  open Classical in
  letI : DecidableEq (SimpleGraph (Fin n)) := decEq _
  letI : ∀ G : SimpleGraph (Fin n), DecidableRel G.Adj := fun _ => decRel _
  -- n = 0: when there are no vertices, the only graph is the empty graph
  if n = 0 then
    if S = Set.univ then 1 else 0
  else if h : S.Finite then
    h.toFinset.sum fun G =>
      ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α)))
  else ⊤

/-- For n = 0, handles the measure equality for disjoint unions in the subsingleton case. -/
lemma tsum_measureOf_disjoint_eq_measureOf_iUnion_n_zero (α : ℝ)
    (hf : ℕ → Set (SimpleGraph (Fin 0)))
    (hDisj : Pairwise (Function.onFun Disjoint hf)) :
    ∑' i, measureOf 0 α (hf i) = measureOf 0 α (⋃ i, hf i) := by
  classical
  by_cases hU : (⋃ i, hf i) = Set.univ
  · -- Union is univ: both sides equal 1
    have hRHS : measureOf 0 α (⋃ i, hf i) = 1 := by
      simp only [measureOf]
      exact if_pos hU
    -- By disjointness, at most one hf i can be univ (others must be empty)
    have hsum_le_one : ∀ s : Finset ℕ, (∑ i ∈ s, measureOf 0 α (hf i)) ≤ 1 := by
      intro s
      by_cases hex : ∃ i ∈ s, hf i = Set.univ
      · -- Exactly one index i0 has hf i0 = univ; all others are empty
        rcases hex with ⟨i0, hi0s, hi0_univ⟩
        have hothers_zero : ∀ j ∈ s, j ≠ i0 → measureOf 0 α (hf j) = 0 := by
          intro j _ hne
          have hDisj_ij : Disjoint (hf i0) (hf j) := by
            have h := hDisj hne
            simp only [Function.onFun] at h
            exact h.symm
          have hj_empty : hf j = ∅ := by
            rw [hi0_univ] at hDisj_ij
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hx_univ : x ∈ Set.univ := Set.mem_univ x
            exact Set.disjoint_right.mp hDisj_ij hx hx_univ
          simp only [measureOf, hj_empty, Set.empty_ne_univ, if_false, if_true]
        calc (∑ i ∈ s, measureOf 0 α (hf i))
            = (∑ j ∈ s.erase i0, measureOf 0 α (hf j)) + measureOf 0 α (hf i0) := by
              rw [Finset.sum_erase_add _ _ hi0s]
          _ = 0 + 1 := by
              congr 1
              · refine Finset.sum_eq_zero fun j hj => ?_
                exact hothers_zero j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
              · simp only [measureOf]
                exact if_pos hi0_univ
          _ = 1 := by exact AddZeroClass.zero_add 1
          _ ≤ 1 := le_refl 1
      · -- No index has hf i = univ, so all terms are 0
        calc (∑ i ∈ s, measureOf 0 α (hf i))
            = 0 := Finset.sum_eq_zero fun i hi => by
              simp only [measureOf]
              by_cases h_eq : hf i = Set.univ
              · exfalso; exact hex ⟨i, hi, h_eq⟩
              · simp [h_eq]
          _ ≤ 1 := by exact zero_le_one' ENNReal
    -- The tsum equals 1 as well
    have hsum_eq_one : ∑' i, measureOf 0 α (hf i) = 1 := by
      -- We know the tsum is at least 1 (one of the sets is univ)
      have hx : (⊥ : SimpleGraph (Fin 0)) ∈ ⋃ i, hf i := by
        have hx' : (⊥ : SimpleGraph (Fin 0)) ∈ Set.univ := by simp
        rw [← hU] at hx'
        exact hx'
      obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hx
      have hSi0_univ : hf i0 = Set.univ := by
        refine Set.eq_univ_iff_forall.mpr ?_
        intro y
        have : y = (⊥ : SimpleGraph (Fin 0)) := Subsingleton.elim _ _
        rw [this]; exact hi0
      have hone_le_tsum : (1 : ENNReal) ≤ ∑' i, measureOf 0 α (hf i) := by
        calc (1 : ENNReal)
            = measureOf 0 α (hf i0) := by
              simp only [measureOf, hSi0_univ, if_true]
          _ ≤ ∑' i, measureOf 0 α (hf i) := ENNReal.le_tsum i0
      -- And it's at most 1 by the finite sum bound
      have htsum_le_one : ∑' i, measureOf 0 α (hf i) ≤ 1 := by
        calc ∑' i, measureOf 0 α (hf i)
            = ⨆ s : Finset ℕ, ∑ i ∈ s, measureOf 0 α (hf i) := ENNReal.tsum_eq_iSup_sum
          _ ≤ 1 := iSup_le hsum_le_one
      exact le_antisymm htsum_le_one hone_le_tsum
    rw [hsum_eq_one, hRHS]
  · -- Union is not univ: both sides are 0
    have h_zero_terms : ∀ i, measureOf 0 α (hf i) = 0 := by
      intro i
      have : hf i ≠ Set.univ := by
        intro hi
        have : Set.univ ⊆ (⋃ j, hf j) := hi ▸ Set.subset_iUnion hf i
        exact hU (Set.eq_univ_of_univ_subset this)
      simp only [measureOf]
      exact ite_eq_right_iff.mpr fun h => absurd h this
    have hRHS_zero : measureOf 0 α (⋃ i, hf i) = 0 := by
      simp only [measureOf]
      exact ite_eq_right_iff.mpr fun h => absurd h hU
    simp [h_zero_terms, hRHS_zero]

/-- For n ≠ 0, the infinite sum of measures of pairwise disjoint sets equals
    the measure of their union. -/
lemma tsum_measureOf_disjoint_eq_measureOf_iUnion (n : ℕ) (α : ℝ) (hn : n ≠ 0)
    (hf : ℕ → Set (SimpleGraph (Fin n)))
    (hDisj : Pairwise (Function.onFun Disjoint hf)) :
    ∑' i, measureOf n α (hf i) = measureOf n α (⋃ i, hf i) := by
  classical
  -- Every subset of a finite type is finite
  have hUnion_fin : (⋃ i, hf i).Finite := Set.toFinite _
  have hf_fin : ∀ i, (hf i).Finite := fun i => Set.toFinite _

  -- Rewrite RHS using the measure definition
  have hRHS : measureOf n α (⋃ i, hf i) = ∑ G ∈ hUnion_fin.toFinset,
      ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) := by
    simp only [measureOf]
    rw [if_neg hn, dif_pos hUnion_fin]

  -- Rewrite each term in the LHS sum
  have hLHS_terms : ∀ i, measureOf n α (hf i) = ∑ G ∈ (hf_fin i).toFinset,
      ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) := fun i => by
    simp only [measureOf]
    rw [if_neg hn, dif_pos (hf_fin i)]

  -- For each G in the union, it appears in exactly one hf i
  have h_support : ∀ G ∈ hUnion_fin.toFinset, ∃! i, G ∈ (hf_fin i).toFinset := by
    intro G hG
    have : G ∈ ⋃ i, hf i := hUnion_fin.mem_toFinset.mp hG
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
    use i
    constructor
    · exact (hf_fin i).mem_toFinset.mpr hi
    · intros j hj
      by_contra hij
      have : Disjoint (hf i) (hf j) := by
        have := hDisj (Ne.symm hij)
        rwa [Function.onFun] at this
      have hGi : G ∈ hf i := (hf_fin i).mem_toFinset.mp ((hf_fin i).mem_toFinset.mpr hi)
      have hGj : G ∈ hf j := (hf_fin j).mem_toFinset.mp hj
      exact Set.disjoint_left.mp this hGi hGj

  -- For each G, the sum ∑' i, [indicator] = single value
  have h_point : ∀ G ∈ hUnion_fin.toFinset,
      ∑' i, (if G ∈ (hf_fin i).toFinset
        then ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α)))
        else 0) = ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) := by
    intro G hG
    obtain ⟨i, hi, huniq⟩ := h_support G hG
    -- The sum has exactly one nonzero term (at index i)
    have h_others_zero : ∀ j, j ≠ i → G ∉ (hf_fin j).toFinset := by
      intro j hne hcontra
      exact hne (huniq j hcontra)
    -- Use tsum_eq_single to isolate the single nonzero term
    convert tsum_eq_single i (fun j hne => if_neg (h_others_zero j hne)) using 1
    exact (if_pos hi).symm

  -- Main calculation: swap sum order and use h_point
  calc (∑' i, measureOf n α (hf i))
      = ∑' i, ∑ G ∈ (hf_fin i).toFinset,
          ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) := by
          congr 1; ext i; exact hLHS_terms i
    _ = ∑' i, ∑ G ∈ hUnion_fin.toFinset,
          (if G ∈ (hf_fin i).toFinset
            then ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α)))
            else 0) := by
          -- Sum over (hf_fin i).toFinset equals sum over union with indicator
          congr 1; ext i
          have h_subset : (hf_fin i).toFinset ⊆ hUnion_fin.toFinset := by
            intro G hG
            have : G ∈ hf i := (hf_fin i).mem_toFinset.mp hG
            have : G ∈ ⋃ j, hf j := Set.mem_iUnion_of_mem i this
            exact hUnion_fin.mem_toFinset.mpr this
          rw [← Finset.sum_filter]
          congr 1
          ext G
          simp only [Finset.mem_filter]
          exact ⟨fun hG => ⟨h_subset hG, hG⟩, fun ⟨_, hG⟩ => hG⟩
    _ = ∑ G ∈ hUnion_fin.toFinset, ∑' i,
          (if G ∈ (hf_fin i).toFinset
            then ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α)))
            else 0) := by
          -- order swap
          have h1 : (∑' i, ∑ G ∈ hUnion_fin.toFinset,
              (if G ∈ (hf_fin i).toFinset
              then ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) else 0)) =
            (∑' i, ∑' (G : {x // x ∈ hUnion_fin.toFinset}),
              (if (G : SimpleGraph (Fin n)) ∈ (hf_fin i).toFinset
              then ENNReal.ofReal
              (graphProbabilityProduct (G : SimpleGraph (Fin n)) ((n : ℝ) ^ (-α))) else 0))
              := by
            congr 1; ext i
            exact (Finset.tsum_subtype hUnion_fin.toFinset _).symm
          rw [h1, ENNReal.tsum_comm]
          exact Finset.tsum_subtype hUnion_fin.toFinset
            (fun G => ∑' i, if G ∈ (hf_fin i).toFinset
              then ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α)))
              else 0)
    _ = ∑ G ∈ hUnion_fin.toFinset,
          ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) := by
          refine Finset.sum_congr rfl fun G hG => ?_
          exact h_point G hG
    _ = measureOf n α (⋃ i, hf i) := hRHS.symm

/-- Proof that the edge-probability measure is an outer measure. -/
noncomputable def OuterMeasure (n : ℕ) (α : ℝ) :
    MeasureTheory.OuterMeasure (SimpleGraph (Fin n)) :=
    {
        measureOf := measureOf n α
        empty := by
          simp only [measureOf]
          split_ifs with hn hempty hfin
          · -- Case n = 0 and ∅ = Set.univ
            exact absurd hempty Set.empty_ne_univ
          · -- Case n = 0 and ∅ ≠ Set.univ: measureOf ∅ = 0
            rfl
          · -- Case n ≠ 0 and ∅ is finite: sum over empty finset = 0
            simp
          · -- Case n ≠ 0 and ∅ is not finite
            simp at hfin
        mono := by
          intros S T hST
          simp only [measureOf]
          split_ifs with hn hS_univ hT_univ hS_fin hT_fin
          · rfl                                    -- Case 1: n=0, S=univ, T=univ
          · have : T = Set.univ := Set.eq_univ_of_univ_subset (hS_univ ▸ hST)
            exact absurd this hT_univ              -- Case 2: n=0, S=univ, T≠univ
          · exact zero_le _                        -- Case 3: n=0, S≠univ, T=univ
          · rfl                                    -- Case 4: n=0, S≠univ, T≠univ
          · apply Finset.sum_le_sum_of_subset      -- Case 5: n≠0, S finite, T finite
            intro x hx
            simp [Set.Finite.mem_toFinset] at hx ⊢
            exact hST hx
          · exact le_top                           -- Case 6: n≠0, S finite, T infinite
          · exfalso                                -- Case 7: n≠0, S infinite, T finite
            rename_i hT_finite
            exact hT_fin (Set.Finite.subset hT_finite hST)
          · rfl                                    -- Case 8: n≠0, S infinite, T infinite
        iUnion_nat := by
          intros S hS
          by_cases hn : n = 0
          · -- Case: n = 0: Apply the lemma
            subst hn
            have : ∑' i, measureOf 0 α (S i) = measureOf 0 α (⋃ i, S i) :=
              tsum_measureOf_disjoint_eq_measureOf_iUnion_n_zero α S hS
            exact le_of_eq this.symm
          · -- Case: n ≠ 0
            simp only [measureOf, if_neg hn]
            split_ifs with hs_Fin
            · -- `n ≠ 0`, union is finite: Apply the lemma showing equality for disjoint unions
              have hS_fin : ∀ i, (S i).Finite :=
                fun i => Set.Finite.subset hs_Fin (Set.subset_iUnion S i)
              classical
              suffices ∑ G ∈ hs_Fin.toFinset,
                ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) ≤
                  ∑' i, ∑ G ∈ (hS_fin i).toFinset,
                  ENNReal.ofReal (graphProbabilityProduct G ((n : ℝ) ^ (-α))) by
                convert this using 2
                ext i
                exact dif_pos (hS_fin i)
              have : measureOf n α (⋃ i, S i) = ∑' i, measureOf n α (S i) :=
                (tsum_measureOf_disjoint_eq_measureOf_iUnion n α hn S hS).symm
              simp only [measureOf, if_neg hn, dif_pos hs_Fin, dif_pos (hS_fin _)] at this
              exact le_of_eq this
            · -- `n ≠ 0`, `∪ i, S i` is infinite
              -- This is impossible: SimpleGraph (Fin n) is a finite type, so any subset is finite
              exfalso
              exact hs_Fin (Set.toFinite (⋃ i, S i))
    }

/-- proof that the edge-probability outer measure is a measure. -/
noncomputable def Measure (n : ℕ) (α : ℝ):
    Measure (SimpleGraph (Fin n)) :=
  let μ₀ := OuterMeasure n α
  { toOuterMeasure := μ₀
    m_iUnion := by
      intros hf hMeas hDisj
      apply le_antisymm
      · exact μ₀.iUnion_nat hf hDisj
      · classical
        by_cases hn : n = 0
        · -- n = 0: Apply the lemma
          subst hn
          have : ∑' i, μ₀ (hf i) = μ₀ (⋃ i, hf i) := by
            show ∑' i, measureOf 0 α (hf i) = measureOf 0 α (⋃ i, hf i)
            exact tsum_measureOf_disjoint_eq_measureOf_iUnion_n_zero α hf hDisj
          exact le_of_eq this
        · -- n ≠ 0: Apply the lemma showing equality for disjoint unions
          have : ∑' i, μ₀ (hf i) = μ₀ (⋃ i, hf i) := by
            show ∑' i, measureOf n α (hf i) = measureOf n α (⋃ i, hf i)
            exact tsum_measureOf_disjoint_eq_measureOf_iUnion n α hn hf hDisj
          exact le_of_eq this
    trim_le := fun s => by
      have hs : MeasurableSet s := trivial
      exact (OuterMeasure.trim_eq μ₀ hs).le
  }

/-- Lemma broader than Shelah-Spencer: covers very sparse graphs as long as
edge probability is really a probability, where μ(Univ) = 1 with n^{-α} ∈ [0, 1]. -/
lemma ProbabilityMeasure (n : ℕ) (α : ℝ) (hα : α ≥ 0):
    IsProbabilityMeasure (Measure n α) := by
  constructor
  -- Goal: (Measure n α) Set.univ = 1
  -- Split into three cases based on n
  rcases n with _ | _ | n
  · -- Case n = 0: Space is subsingleton, measure assigns 1 to univ
    show (Measure 0 α) Set.univ = 1
    change (OuterMeasure 0 α) Set.univ = 1
    show measureOf 0 α Set.univ = 1
    simp only [measureOf]
    simp
  · -- Case n = 1: Single vertex, unique graph has measure 1
    show (Measure 1 α) Set.univ = 1
    change (OuterMeasure 1 α) Set.univ = 1
    show measureOf 1 α Set.univ = 1
    simp only [measureOf]
    simp only [if_neg (by norm_num : 1 ≠ 0)]
    -- Set.univ is finite
    have h_fin : (Set.univ : Set (SimpleGraph (Fin 1))).Finite := Set.toFinite _
    rw [dif_pos h_fin]
    -- The space SimpleGraph (Fin 1) has exactly one graph (no edges possible)
    -- Since there's only one graph, the sum is over a singleton
    have h_singleton : ∃ G, h_fin.toFinset = {G} := by
      use ⊥  -- The graph with 1 vertex and no edge
      ext G'
      simp
    obtain ⟨G, hG_eq⟩ := h_singleton
    rw [hG_eq]
    simp only [Finset.sum_singleton]
    -- graphProbabilityProduct for n = 1 is 1 (empty product over no pairs); see `h_empty` below
    classical
    have h_prod_eq_one : graphProbabilityProduct G (((1 : ℕ) : ℝ) ^ (-α)) = 1 := by
      unfold graphProbabilityProduct
      have h_empty : ((Finset.univ : Finset (Fin 1)).product Finset.univ).filter
          (fun (x, y) => x < y) = ∅ := by
        ext ⟨x, y⟩
        simp [Finset.mem_filter]
      rw [h_empty]
      simp [Finset.prod_empty]
    rw [h_prod_eq_one]
    norm_num
  · -- Case n ≥ 2: Arithmetic computation using Finset.sum_pow_mul_eq_add_pow
    -- We have new n := n.succ.succ, so n ≥ 2
    show (Measure (n + 2) α) Set.univ = 1
    change (OuterMeasure (n + 2) α) Set.univ = 1
    show measureOf (n + 2) α Set.univ = 1
    simp only [measureOf]
    simp only [if_neg (by norm_num : n + 2 ≠ 0)]
    have h_fin : (Set.univ : Set (SimpleGraph (Fin (n + 2)))).Finite := Set.toFinite _
    rw [dif_pos h_fin]
    classical

    -- Note: `graphProbabilityProduct` already computes ∏_{pairs} [p if edge, (1-p) if not]
    -- by definition, so the product structure is built-in.

    -- Step 1: Apply Key: ∑_G ∏_{pairs (x,y)} [p if (x,y) ∈ G, (1-p) if not]
    --    = ∏_{pairs (x,y)} (p + (1-p))
    -- This is the crucial combinatorial identity
    have step1_apply_prod_add :
        let p := ((n + 2 : ℕ) : ℝ) ^ (-α)
        ∑ G ∈ h_fin.toFinset,
          ENNReal.ofReal (graphProbabilityProduct G p) =
        ENNReal.ofReal (∏ _pair ∈ (Finset.univ.product Finset.univ).filter
          (fun (x, y) => (x : Fin (n + 2)) < y),
          (p + (1 - p))) := by
      classical
      intro p
      set edges := (Finset.univ.product Finset.univ).filter
        (fun (x, y) => (x : Fin (n + 2)) < y) with h_edges
      let Edge := {e : (Fin (n + 2) × Fin (n + 2)) // e ∈ edges}
      -- All possible ((n + 2) choose 2) edges
      haveI : Fintype Edge := inferInstance
      have hp : p = ((n + 2 : ℕ) : ℝ) ^ (-α) := rfl
      have hp_nonneg : 0 ≤ p := by
        have : 0 ≤ ((n + 2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.zero_le (n + 2)
        have := Real.rpow_nonneg this (-α)
        rw [← hp] at this; trivial
      have hp_le_one : p ≤ 1 := by
        have hbase_ge_one : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + 1))
        have hexp_nonpos : -α ≤ 0 := neg_nonpos.mpr hα
        have := Real.rpow_le_one_of_one_le_of_nonpos hbase_ge_one hexp_nonpos
        simpa [hp] using this
      have h_univ : h_fin.toFinset = (Finset.univ :
          Finset (SimpleGraph (Fin (n + 2)))) := by
        ext G
        simp
      -- Define the equivalence between graphs and edge configurations as a `let`-definition
      -- for subsequent access to its construction
      let h_graph_equiv : (SimpleGraph (Fin (n + 2))) ≃ (Edge → Bool) :=
        { toFun := fun G e => G.Adj e.val.1 e.val.2
          invFun := fun cfg =>
            -- cfg : Edge → Bool specifies which edges are present in a graph and which aren't
            { Adj := fun v w => if h : v < w then
                cfg ⟨(v, w), by simp [h_edges]; exact h⟩
              else if h' : w < v then
                cfg ⟨(w, v), by simp [h_edges]; exact h'⟩
              else False
              symm := by
                intro v w hvw
                by_cases h : v < w
                · -- Case: v < w, so Adj v w uses cfg ⟨(v, w), _⟩
                  simp only [h, ↓reduceDIte] at hvw ⊢
                  by_cases hwv : w < v
                  · exact absurd (lt_trans h hwv) (lt_irrefl v)
                  · -- Need to show: Adj w v = cfg ⟨(v, w), _⟩
                    -- Since ¬(w < v), Adj w v goes to second branch
                    simp only [hwv] at hvw ⊢
                    -- Goal: (if h : False then ... else cfg ⟨(v, w), _⟩) = true
                    -- Need to simplify the if with False condition
                    convert hvw using 1
                · by_cases h' : w < v
                  · -- Case: w < v (and ¬v < w), so Adj v w uses cfg ⟨(w, v), _⟩
                    simp only [h, h', ↓reduceDIte] at hvw ⊢
                    by_cases hvw' : v < w
                    · exact absurd (lt_trans h' hvw') (lt_irrefl w)
                    · -- Goal is already hvw : cfg ⟨(w, v), _⟩ = true
                      exact hvw
                  · -- Case: ¬v < w and ¬w < v, so v = w, contradiction with Adj v w
                    simp only [h, h', ↓reduceDIte] at hvw
                    -- hvw says decide False = true, which is impossible
                    cases hvw
              loopless := by
                intro v
                simp }
          left_inv := by
            intro G
            ext v w
            simp only
            by_cases hvw : v < w
            · simp [hvw]
            · by_cases hwv : w < v
              · simp [hvw, hwv]
                exact (G.adj_comm v w).symm
              · simp [hvw, hwv]
                have : v = w := by
                  exact le_antisymm (le_of_not_gt hwv) (le_of_not_gt hvw)
                rw [this]
                exact G.loopless w
          right_inv := by
            intro cfg
            ext e
            simp only
            obtain ⟨⟨v, w⟩, h_mem⟩ := e
            simp [h_edges] at h_mem
            simp [h_mem] }
      have h_sum_reindex :
          ∑ G ∈ h_fin.toFinset, ENNReal.ofReal (graphProbabilityProduct G p) =
          ∑ cfg : Edge → Bool,
            ENNReal.ofReal (graphProbabilityProduct (h_graph_equiv.symm cfg) p) := by
        -- Reindex using the equivalence in `h_graph_equiv`
        rw [h_univ, ← Fintype.sum_equiv h_graph_equiv
          (fun G => ENNReal.ofReal (graphProbabilityProduct G p))
          (fun cfg => ENNReal.ofReal (graphProbabilityProduct (h_graph_equiv.symm cfg) p))
          (fun cfg => by simp [Equiv.symm_apply_apply])]
      have h_product_rewrite :
          ∀ cfg : Edge → Bool,
            graphProbabilityProduct (h_graph_equiv.symm cfg) p =
            ∏ e ∈ edges.attach, (if cfg e then p else (1 - p)) := by
            intros cfg
            -- use explicit construction in `h_graph_equiv` and `graphProbabilityProduct`
            unfold graphProbabilityProduct
            -- The graph (`h_graph_equiv.symm cfg`) has adjacency determined by `cfg`
            set G := h_graph_equiv.symm cfg with hG
            -- The filtered set equals edges
            have h_filter_eq : ((Finset.univ.product Finset.univ).filter
                (fun (x, y) => x < y)) = edges := by
              rw [← h_edges]
            rw [h_filter_eq]
            -- Transform the RHS to work over edges using prod_bij
            symm
            refine Finset.prod_bij (fun e _ => e.val) ?_ ?_ ?_ ?_
            · -- e.val ∈ edges
              intro e _
              exact e.property
            · -- The function values match
              intro ⟨⟨v, w⟩, h_mem⟩ _
              simp only
              simp at this
              -- By construction of G = h_graph_equiv.symm cfg, we have:
              -- G.Adj v w ↔ cfg ⟨(v, w), h_mem⟩ = true
              by_cases h_cfg : cfg ⟨(v, w), h_mem⟩
              · simp
              · simp
            · -- surjectivity
              -- Goal: `∀ b ∈ edges, ∃ a, ∃ (ha : a ∈ edges.attach), (fun e x ↦ ↑e) a ha = b`
              intro b h_b
              exact ⟨⟨b, h_b⟩, Finset.mem_attach _ _, rfl⟩
            · -- inj.
              -- Goal: `∀ (a : { x // x ∈ edges }) (ha : a ∈ edges.attach), (if cfg a = true then p
              -- else 1 - p) = match (fun e x ↦ ↑e) a ha with | (x, y) => if G.Adj x y then p else
              -- 1 - p`
              intro ⟨⟨v, w⟩, h_mem⟩ _
              simp only
              have h_mem_edges : (v, w) ∈ edges := h_mem
              simp [h_edges] at this h_mem_edges
              -- By construction of G = h_graph_equiv.symm cfg, we have:
              -- G.Adj v w ↔ cfg ⟨(v, w), h_mem⟩ = true
              have h_adj : G.Adj v w ↔ cfg ⟨(v, w), h_mem⟩ = true := by
                rw [hG]
                simp only [h_graph_equiv, Equiv.coe_fn_symm_mk]
                simp only [h_mem_edges, ↓reduceDIte]
              by_cases h_cfg : cfg ⟨(v, w), h_mem⟩
              · have h_cfg_pos: G.Adj v w := h_adj.mpr h_cfg
                simp [h_cfg_pos, h_cfg] -- intermediate notes: here h_cfg_pos/negs are needed,
                -- have h_mem_edges are also needed
                -- as opposed to ll. 676-681 above.
              · have h_cfg_neg: ¬G.Adj v w := mt h_adj.mp (by simp [h_cfg])
                simp [h_cfg_neg, h_cfg]
      have h_sum_products :
          ∑ cfg : Edge → Bool,
            ENNReal.ofReal (graphProbabilityProduct (h_graph_equiv.symm cfg) p) =
          ∑ cfg : Edge → Bool,
            ENNReal.ofReal (∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) := by
        congr 1
        ext cfg
        rw [h_product_rewrite cfg]
      have h_nonneg :
          ∀ cfg : Edge → Bool,
            0 ≤ ∏ e ∈ edges.attach, (if cfg e then p else (1 - p)) := by
        intro cfg
        apply Finset.prod_nonneg
        intro e _
        by_cases h : cfg e
        · have : 0 ≤ p := hp_nonneg
          simpa [h, hp] using this
        · have : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
          simpa [h, hp] using this
      have h_ofReal_sum :
          ∑ cfg : Edge → Bool,
            ENNReal.ofReal (∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) =
          ENNReal.ofReal (∑ cfg : Edge → Bool,
            ∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro cfg _
        exact h_nonneg cfg
      have h_factorization :
          (∑ cfg : Edge → Bool,
            ∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) =
          ∏ e ∈ edges.attach, (p + (1 - p)) := by
        classical
        have h_attach :
            edges.attach = (Finset.univ : Finset Edge) := by
          ext e
          simp [Edge]
        have h_sum :
            (∑ cfg : Edge → Bool,
                ∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) =
            ∑ cfg : Edge → Bool,
                ∏ e : Edge, (if cfg e then p else (1 - p)) := by
          congr 1
          ext cfg
          rw [h_attach]
        have h_prod :
            ∑ cfg : Edge → Bool, ∏ e : Edge, (if cfg e then p else (1 - p)) =
            ∏ e : Edge, (p + (1 - p)) := by
          classical
          have h_sum_pi :
              ∑ cfg : Edge → Bool, ∏ e : Edge, (if cfg e then p else (1 - p)) =
              ∑ cfg ∈ Fintype.piFinset fun _ : Edge ↦ (Finset.univ : Finset Bool),
                ∏ e : Edge, (if cfg e then p else (1 - p)) := by
            have : Fintype.piFinset (fun _ : Edge ↦ (Finset.univ : Finset Bool)) = Finset.univ := by
              ext cfg
              simp [Fintype.mem_piFinset]
            rw [this]
          have h_prod_sum :
              ∑ cfg ∈ Fintype.piFinset fun _ : Edge ↦ (Finset.univ : Finset Bool),
                ∏ e : Edge, (if cfg e then p else (1 - p)) =
              ∏ e : Edge, ∑ b ∈ (Finset.univ : Finset Bool), (if b then p else (1 - p)) := by
            simpa using
              (Finset.sum_prod_piFinset
                (κ := Bool)
                (ι := Edge)
                (s := (Finset.univ : Finset Bool))
                (g := fun _ b => if b then p else (1 - p)))
          have h_bool :
              ∏ e : Edge, ∑ b ∈ (Finset.univ : Finset Bool), (if b then p else (1 - p)) =
              ∏ e : Edge, (p + (1 - p)) := by
            simp
          exact h_sum_pi.trans (h_prod_sum.trans h_bool)
        calc (∑ cfg : Edge → Bool, ∏ e ∈ edges.attach, (if cfg e then p else (1 - p)))
            = ∑ cfg : Edge → Bool, ∏ e : Edge, (if cfg e then p else (1 - p)) := h_sum
          _ = ∏ e : Edge, (p + (1 - p)) := h_prod
          _ = ∏ e ∈ edges.attach, (p + (1 - p)) := by rw [← h_attach]
      have h_final :
          ENNReal.ofReal (∑ cfg : Edge → Bool,
            ∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) =
          ENNReal.ofReal (∏ _pair ∈
            (Finset.univ.product Finset.univ).filter
              (fun (x, y) => (x : Fin (n + 2)) < y),
            (p + (1 - p))) := by
        rw [h_factorization]
        congr 1
        calc
          ∏ e ∈ edges.attach, (p + (1 - p))
              = ∏ _pair ∈ edges, (p + (1 - p)) := by
                  refine Finset.prod_bij (fun e _ => e.val) ?_ ?_ ?_ ?_
                  · intro e _; exact e.property
                  · intro a₁ ha₁ a₂ ha₂ h; exact Subtype.ext h
                  · intro b hb; exact ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩
                  · intro _ _; rfl
              _ = ∏ _pair ∈
                (Finset.univ.product Finset.univ).filter
                  (fun (x, y) => (x : Fin (n + 2)) < y),
                (p + (1 - p)) := by
                simp only [h_edges]
      calc
        ∑ G ∈ h_fin.toFinset, ENNReal.ofReal (graphProbabilityProduct G p)
            = ∑ cfg : Edge → Bool,
                ENNReal.ofReal (graphProbabilityProduct (h_graph_equiv.symm cfg) p) :=
          h_sum_reindex
        _ = ∑ cfg : Edge → Bool,
                ENNReal.ofReal (∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) :=
          h_sum_products
        _ = ENNReal.ofReal (∑ cfg : Edge → Bool,
                ∏ e ∈ edges.attach, (if cfg e then p else (1 - p))) := h_ofReal_sum
        _ = ENNReal.ofReal (∏ _pair ∈ edges, (p + (1 - p))) := h_final

    -- Step 2: Simplify product to power form
    -- ∏_{pairs} (p + (1-p)) = (p + (1-p))^(# of pairs)
    have step2_product_to_power :
        let p := ((n + 2 : ℕ) : ℝ) ^ (-α)
        (∏ _pair ∈ (Finset.univ.product Finset.univ).filter
          (fun (x, y) => (x : Fin (n + 2)) < y),
          (p + (1 - p))) = (p + (1 - p)) ^ ((n + 2).choose 2) := by
      intro p
      have h_card' (m : ℕ): ((Finset.univ.product Finset.univ).filter
      (fun (x, y) => (x : Fin (m + 1)) < y)).card = (m + 1).choose 2 := by
        erw [ Finset.card_filter ];
        erw [ Finset.sum_product ] ; simp
        -- The sum of the number of elements greater than $i$ for each $i$ in $Fin (m + 1)$ equals
        -- the sum of the first $m$ natural numbers.
        have h_sum : ∑ x : Fin (m + 1),
          (Finset.univ.filter (fun y => x < y)).card = ∑ i ∈ Finset.range (m + 1), (m - i) := by
          simp +decide [Finset.filter_lt_eq_Ioi];
          rw [ Finset.sum_range ];
        rw [ h_sum, Nat.choose_two_right ];
        -- The sum of the first $m$ natural numbers is given by the formula $\frac{m(m+1)}{2}$.
        have h_sum_formula : ∑ i ∈ Finset.range (m + 1), (m - i) = ∑ i ∈ Finset.range (m + 1),
          i := by
          conv_rhs => rw [ ← Finset.sum_flip ];
        exact h_sum_formula.trans ( Finset.sum_range_id _ )
      -- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/
      -- Number.20of.20pairs.20on.20.60Fin.20.28n.29.60/near/544300248
      have h_card : ((Finset.univ.product Finset.univ).filter
          (fun (x, y) => (x : Fin (n + 2)) < y)).card = (n + 2).choose 2 := by
        apply h_card' (n + 1) -- Need: |{(x,y) : Fin m × Fin m | x < y}| = m choose 2
      rw [← h_card, Finset.prod_const]

    -- Step 3: Simplify (p + (1-p))^k = 1^k = 1
    have step3_simplify :
        ∀ p : ℝ,
        ENNReal.ofReal ((p + (1 - p)) ^ ((n + 2).choose 2)) = 1 := by
      intro p
      have h_add : p + (1 - p) = 1 := by ring
      rw [h_add]; simp [one_pow]

    -- Combine all steps

    -- Let p be the edge probability used above
    set p := ((n + 2 : ℕ) : ℝ) ^ (-α) with hp
    have h1 :
        (∑ G ∈ h_fin.toFinset,
          ENNReal.ofReal (graphProbabilityProduct G p))
        = ENNReal.ofReal (∏ _pair ∈ (Finset.univ.product Finset.univ).filter
            (fun (x, y) => (x : Fin (n + 2)) < y), (p + (1 - p))) := by
      -- apply Step 1 and rewrite the chosen p
      simpa [hp] using step1_apply_prod_add
    have h2 :
        ENNReal.ofReal (∏ _pair ∈ (Finset.univ.product Finset.univ).filter
            (fun (x, y) => (x : Fin (n + 2)) < y), (p + (1 - p)))
        = ENNReal.ofReal ((p + (1 - p)) ^ ((n + 2).choose 2)) := by
      -- apply Step 2 inside ENNReal.ofReal
      -- coerce both sides with ofReal
      simp only [hp]
      exact congrArg ENNReal.ofReal step2_product_to_power
    have h3 : ENNReal.ofReal ((p + (1 - p)) ^ ((n + 2).choose 2)) = 1 := by
      exact step3_simplify p

    calc
      ∑ G ∈ h_fin.toFinset, ENNReal.ofReal (graphProbabilityProduct G p)
          = ENNReal.ofReal (∏ _pair ∈ (Finset.univ.product Finset.univ).filter
              (fun (x, y) => (x : Fin (n + 2)) < y), (p + (1 - p))) := h1
      _ = ENNReal.ofReal ((p + (1 - p)) ^ ((n + 2).choose 2)) := h2
      _ = 1 := h3
end ShelahSpencer
