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

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
/-!
# Probability utilities for random graph statements

This file collects probability theory prerequisites that will be used when studying
finite random graphs such as `G(n, p)`, particularly `G(n, n^{-α})`.
The key lemma states that for each `n`, the measure on `G(n, n^{-α})` defined by cumulating a graph's
edge and non-edge probabilities (see `def graphProbabilityProduct `) is a probability measure.

*References*:
[Zero-one laws for sparse random graphs]
Journal of the American Mathematical Society, 1(1), 97-115.
by *S. Shelah* and *J. Spencer*

[Range and degree of realizability of formulas in the restricted predicate calculus]
Cybernetics, 5(2), 142-154.
by *Glebskii, Y. V., Kogan, D. I., Liogon'kiI, M. I., & Talanov, V. A. (1969)* (for α = 0)
-/


namespace ShelahSpencer
open MeasureTheory
open scoped BigOperators

instance MeasurableSpace' {E: Type*}[Fintype E]: MeasurableSpace (SimpleGraph (E)) :=
{
    MeasurableSet' := fun _ => True
    measurableSet_empty := trivial
    measurableSet_compl:= by exact fun s a ↦ a
    measurableSet_iUnion:= fun _ _ => trivial
}

/-- Edge probability p-/
def probabilityEdge' {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (ab : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y ↦ if G.Adj x y then p else (1 - p), by simp [SimpleGraph.adj_comm]⟩ ab
/-- `μ(G)` for `G` with Fintype vertices -/
def graphProbabilityProduct' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) : ℝ :=
  (Finset.univ.sym2 \ Finset.univ.image Sym2.diag).prod <| probabilityEdge' G p



/-- `μ(G)` for `G` with edge probability `p(n) := n^{-α}`,
 where `V := E where |E| = n` -/
noncomputable def measureOf' {E} [Fintype E] (α : ℝ)
    (S : Set (SimpleGraph E)) : ENNReal :=
  open Classical in
  S.toFinset.sum fun G =>
      ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α)))

lemma tsum_measureOf_disjoint_eq_measureOf_iUnion' {E: Type*}[Fintype E] (α : ℝ)
    (hf : ℕ → Set (SimpleGraph (E)))
    (hDisj : Pairwise (Function.onFun Disjoint hf)) :
    ∑' i, measureOf' α (hf i) = measureOf' α (⋃ i, hf i) := by
    classical

  -- Rewrite RHS using the measure definition
    have hRHS : measureOf' α (⋃ i, hf i) = ∑ G ∈ (⋃ i, hf i),
      ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) := by
        simp only [measureOf']
        -- Note `p(n) := (((Fintype.card E) : ℝ) ^ (-α))`

    have hLHS_terms : ∀ i, measureOf' α (hf i) = ∑ G ∈ (hf i),
        ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) := fun i => by
          simp only [measureOf']

    -- For each `G` in the union, it appears in exactly one `hf i`, thanks to `hDisj`
    have h_support : ∀ G ∈ ⋃ i, hf i, ∃! i, G ∈ (hf i) := by
      intros G hG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hG
      use i
      constructor
      · aesop
      · intros j hj
        by_contra hij
        have : Disjoint (hf i) (hf j) := by
          have := hDisj (Ne.symm hij)
          rwa [Function.onFun] at this
        exact Set.disjoint_left.mp this hi hj

    -- To perform the key order-swap: (summing first over `i` then over `G ∈ hf i`) ↝
    -- (summing over `G` in the union, then over `i` s.t. `G ∈ hf i`), we spell out that
    -- the cofinitely many (in fact all but 1 here, see `h_support`) sets avoiding `G` gets `0`
    -- in the sum. *See* main `calc` step.
      -- `h_point` below is a helpfer for the closing step of this
      -- "infinite sum to finite sum" conversion
    have h_point :  ∀ G ∈ (⋃ i, hf i).toFinset,
      ∑' i, (if G ∈ (hf i)
        then ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α)))
        else 0) = ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) := by
          intro G hG
          -- Convert Finset membership to Set membership
          rw [Set.mem_toFinset] at hG
          obtain ⟨i, hi, huniq⟩ := h_support G hG
          -- The sum has exactly one nonzero term (at index i)
          have h_others_zero : ∀ j, j ≠ i → G ∉ (hf j) := by
            intro j hne hcontra
            exact hne (huniq j hcontra)
          -- Use tsum_eq_single to isolate the single nonzero term
          convert tsum_eq_single i (fun j hne => if_neg (h_others_zero j hne)) using 1
          exact (if_pos hi).symm

    -- Main calculation: swap sum order using `h_point`
    calc (∑' i, measureOf' α (hf i))
      = ∑' i, ∑ G ∈ (hf i),
          ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) := by
          congr 1--- ext i; exact hLHS_terms i
    _ = ∑' i, ∑ G ∈ ⋃ i, hf i,
          (if G ∈ (hf i)
            then ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α)))
            else 0) := by
          -- Sum over (hf_fin i).toFinset equals sum over union with indicator
          congr 1; ext i
          have h_subset : (hf i) ⊆ ⋃ i, hf i := by
            intro G hG
            exact Set.mem_iUnion_of_mem i hG
          rw [← Finset.sum_filter]
          congr 1
          ext G
          simp only [Finset.mem_filter]
          aesop
        -- order swap
    _ = ∑ G ∈ ⋃ i, hf i, ∑' i,
          (if G ∈ (hf i)
            then ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α)))
            else 0) := by
          have h1 : (∑' i, ∑ G ∈ ⋃ i, hf i,
              (if G ∈ (hf i)
              then
              ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) else 0)) =
            (∑' i, ∑' (G : {x // x ∈ (⋃ i, hf i).toFinset}),
              (if (G : SimpleGraph (E)) ∈ (hf i)
              then ENNReal.ofReal
              (graphProbabilityProduct' (G : SimpleGraph E)
              (((Fintype.card E) : ℝ) ^ (-α))) else 0))
              := by
                congr 1; ext i
                exact (Finset.tsum_subtype (⋃ i, hf i).toFinset _).symm
          rw [h1, ENNReal.tsum_comm]
          exact Finset.tsum_subtype (⋃ i, hf i).toFinset
            (fun G => ∑' i, if G ∈ (hf i)
              then ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α)))
              else 0)
    _ = ∑ G ∈ ⋃ i, hf i,
          ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E) : ℝ) ^ (-α))) := by
          refine Finset.sum_congr rfl fun G hG => ?_
          exact h_point G hG
    _ = measureOf' α (⋃ i, hf i) := hRHS.symm

/-- Proof that the edge-probability measure is an outer measure; new version. -/
noncomputable def OuterMeasure' {E: Type*}[Fintype E] (α : ℝ) :
    MeasureTheory.OuterMeasure (SimpleGraph (E)) :=
    {
        measureOf := measureOf' α
        empty := by
          simp only [measureOf']
          simp
        mono := by
          intros S T hST
          simp only [measureOf']
          apply Finset.sum_le_sum_of_subset
          intro x hx
          simp at hx ⊢
          exact hST hx
        iUnion_nat := by
          intros S hS
          have : measureOf' α (⋃ i, S i) = ∑' i, measureOf' α (S i) :=
                (tsum_measureOf_disjoint_eq_measureOf_iUnion' α S hS).symm
          simp only [measureOf'] at this
          exact le_of_eq this
    }

/-- proof that the edge-probability outer measure is a measure; new version. -/
noncomputable def Measure' {E: Type*}[Fintype E] (α : ℝ):
    MeasureTheory.Measure (SimpleGraph (E)) :=
  let μ₀ := OuterMeasure' α
  { toOuterMeasure := μ₀
    m_iUnion := by
      intros hf hMeas hDisj
      apply le_antisymm
      · exact μ₀.iUnion_nat hf hDisj
      · classical
        have : ∑' i, μ₀ (hf i) = μ₀ (⋃ i, hf i) := by
            show ∑' i, measureOf' α (hf i) = measureOf' α (⋃ i, hf i)
            exact tsum_measureOf_disjoint_eq_measureOf_iUnion' α hf hDisj
        exact le_of_eq this
    trim_le := fun s => by
      have hs : MeasurableSet s := trivial
      exact (OuterMeasure.trim_eq μ₀ hs).le
  }

/-- A helper for the proof that this Measure is a probability
-/
lemma probabilityEdge'_eq_edgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (e : Sym2 V) :
    probabilityEdge' G p e = if e ∈ G.edgeSet then p else (1 - p) := by
  classical
  refine Sym2.ind (fun v w => ?_) e
  simp [probabilityEdge', SimpleGraph.mem_edgeSet]

/-- Lemma's `α` range is broader than needed by Shelah-Spencer: covers very sparse graphs as long as
-- μ(Univ) = 1 with n^{-α} ∈ [0, 1]; lemma just says the `Measure'` above are probabilities.
-/
lemma ProbabilityMeasure' {E: Type*} [Fintype E] (α : ℝ) (hα : α ≥ 0):
  IsProbabilityMeasure (Measure' (E := E) α) := by
  classical
  letI : DecidableEq E := Classical.decEq _
  letI : DecidableEq (SimpleGraph E) := Classical.decEq _
  letI : DecidableEq (Sym2 E) := Classical.decEq _

  constructor
  show (Measure' α) Set.univ = 1
  change (OuterMeasure' α) Set.univ = 1
  show (measureOf' (E := E) α) Set.univ = 1

  -- Step 1: Apply key combinatorial identity
  -- ∑_G ∏_{pairs (x,y)} [p if (x,y) ∈ G, (1-p) if not] = ∏_{pairs (x,y)} (p + (1-p))
  have step1_apply_prod_add :
      (Finset.univ : Finset (SimpleGraph E)).sum
          (fun G => ENNReal.ofReal
            (graphProbabilityProduct' G (((Fintype.card E : ℕ) : ℝ) ^ (-α)))) =
      ENNReal.ofReal (∏ _pair ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag),
        (((Fintype.card E : ℕ) : ℝ) ^ (-α) + (1 - ((Fintype.card E : ℕ) : ℝ) ^ (-α)))) := by
    set p := ((Fintype.card E : ℕ) : ℝ) ^ (-α)
    let Edge := {e : Sym2 E // e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag)}
    have hp_nonneg : 0 ≤ p := by
      have : 0 ≤ ((Fintype.card E : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
      simpa [p] using Real.rpow_nonneg this (-α)
    have hp_le_one : p ≤ 1 := by
      classical
      by_cases hcard : Fintype.card E = 0
      · simp [p, hcard]
        by_cases hα_zero : α = 0
        · simp [hα_zero]
        · rw [Real.zero_rpow (neg_ne_zero.mpr hα_zero)]
          norm_num
      · have hbase : (1 : ℝ) ≤ (Fintype.card E : ℕ) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcard)
        have hexp : -α ≤ 0 := neg_nonpos.mpr hα
        simpa [p] using Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
    have diag_mem_iff :
        ∀ e : Sym2 E, e ∈ Finset.univ.image Sym2.diag ↔ e.IsDiag := by
      intro e
      constructor
      · intro h
        obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h
        simpa [hx] using Sym2.diag_isDiag x
      · intro h
        obtain ⟨x, rfl⟩ := (Sym2.isDiag_iff_mem_range_diag e).mp h
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have edges_no_diag :
        ∀ {e : Sym2 E}, e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag) →
         ¬ e.IsDiag := by
      intro e he
      have : e ∉ Finset.univ.image Sym2.diag := by
        have := Finset.mem_sdiff.mp he
        exact this.2
      simpa [diag_mem_iff] using this
    let cfgSet : (Edge → Bool) → Set (Sym2 E) := fun cfg =>
      {e | ∃ h : e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag),
       cfg ⟨e, h⟩ = true}
    -- here through the `let graphEquiv`: ingredients for a Graph ↔ Configuration equivalence
    let graphOfCfg : (Edge → Bool) → SimpleGraph E :=
      fun cfg => SimpleGraph.fromEdgeSet (cfgSet cfg)
    let cfgOfGraph : SimpleGraph E → Edge → Bool :=
      fun G e => decide (e.1 ∈ G.edgeSet)
    have cfgSet_subset :
        ∀ cfg {e}, e ∈ cfgSet cfg → ¬ e.IsDiag := by
      intro cfg e he
      rcases he with ⟨hmem, _⟩
      exact edges_no_diag hmem
    have cfgSet_edgeSet (cfg) :
        (graphOfCfg cfg).edgeSet = cfgSet cfg := by
      have : cfgSet cfg \ {e : Sym2 E | e.IsDiag} = cfgSet cfg := by
        ext e; constructor
        · intro he; exact he.1
        · intro he
          exact ⟨he, cfgSet_subset cfg he⟩
      simpa [graphOfCfg, cfgSet] using
        (SimpleGraph.edgeSet_fromEdgeSet (cfgSet cfg)).trans this
    have cfgSet_cfgOfGraph :
        ∀ G, cfgSet (cfgOfGraph G) = G.edgeSet := by
      intro G
      ext e
      constructor
      · intro he
        rcases he with ⟨hmem, hcfg⟩
        have : decide (e ∈ G.edgeSet) = true := by simpa [cfgOfGraph] using hcfg
        exact of_decide_eq_true this
      · intro he
        have hmem : e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag) := by
          have h_not_diag : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet he
          have h_not_in_image : e ∉ Finset.univ.image Sym2.diag := by
            simpa [diag_mem_iff] using h_not_diag
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h_not_in_image⟩
        exact ⟨hmem, decide_eq_true he⟩
    have cfg_mem_iff :
        ∀ cfg (e : Edge), e.1 ∈ (graphOfCfg cfg).edgeSet ↔ cfg e = true := by
      intro cfg e
      constructor
      · intro h
        have hset : e.1 ∈ cfgSet cfg := by
          rw [← cfgSet_edgeSet]
          exact h
        rcases hset with ⟨hmem, hcfg⟩
        have : e = ⟨e.1, hmem⟩ := Subtype.ext rfl
        rw [this]
        exact hcfg
      · intro hcfg
        have htrue : cfg ⟨e.1, e.2⟩ = true := by simpa using hcfg
        have hset : e.1 ∈ cfgSet cfg := by
          exact ⟨e.2, by simpa [cfgSet] using htrue⟩
        simpa [graphOfCfg, cfgSet_edgeSet] using hset
    have graph_cfg_left :
        Function.LeftInverse graphOfCfg cfgOfGraph := by
      intro G
      simp [cfgSet_cfgOfGraph, graphOfCfg]
    have graph_cfg_right :
        Function.RightInverse graphOfCfg cfgOfGraph := by
      intro cfg
      funext e
      by_cases hcfg : cfg e = true
      · have hmem : e.1 ∈ (graphOfCfg cfg).edgeSet := (cfg_mem_iff cfg e).mpr hcfg
        simp [cfgOfGraph, hcfg, hmem]
      · have : e.1 ∉ (graphOfCfg cfg).edgeSet := by
          intro h
          exact hcfg ((cfg_mem_iff cfg e).mp h)
        simp [cfgOfGraph, hcfg, this]
    -- an intuitive equivalence Graph ↔ Configs
    let graphEquiv : (SimpleGraph E) ≃ (Edge → Bool) :=
      { toFun := cfgOfGraph
        invFun := graphOfCfg
        left_inv := graph_cfg_left
        right_inv := graph_cfg_right }
    have h_sum_reindex :
        (Finset.univ : Finset (SimpleGraph E)).sum
            (fun G => ENNReal.ofReal (graphProbabilityProduct' G p)) =
        (Finset.univ : Finset (Edge → Bool)).sum
            (fun cfg => ENNReal.ofReal (graphProbabilityProduct' (graphOfCfg cfg) p)) := by
      refine (Fintype.sum_equiv graphEquiv.symm
          (fun cfg => ENNReal.ofReal (graphProbabilityProduct' (graphOfCfg cfg) p))
          (fun G => ENNReal.ofReal (graphProbabilityProduct' G p))
          (fun cfg => ?_)).symm
      -- simp [graphEquiv]
      simp only [graphEquiv, Equiv.coe_fn_symm_mk]
      classical
      -- align the (definitionally equal) decidable instances for `Adj`
      have hinst :
          (fun a b =>
              Classical.propDecidable ((graphOfCfg cfg).Adj a b)) =
            (fun a b =>
              SimpleGraph.instDecidableRelAdjFromEdgeSetOfDecidablePredSym2MemSetOfDecidableEq
                (cfgSet cfg) a b) := by
        funext a b
        apply Subsingleton.elim
      classical
      aesop
      -- simpa [hinst]
    have h_product_rewrite :
        ∀ cfg : Edge → Bool,
          graphProbabilityProduct' (graphOfCfg cfg) p =
            ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
            (if cfg e = true then p else (1 - p)) := by
      intro cfg
      set G := graphOfCfg cfg with hG
      rw [graphProbabilityProduct']
      symm
      -- Prove using Finset.prod_bij
      refine Finset.prod_bij (fun (e : Edge) _ => e.val) ?_ ?_ ?_ ?_
      · -- membership
        intro e _
        simp only
        convert e.property
      · -- injectivity
        intro a₁ a₂ ha₁ ha₂ h
        simp only at h
        exact Subtype.ext h
      · -- surjectivity
        intro b hb
        simp only at hb
        refine ⟨⟨b, ?_⟩, Finset.mem_attach _ _, rfl⟩
        convert hb
      · -- values match
        intro e he
        simp only
        rw [probabilityEdge'_eq_edgeSet]
        have h_iff : e.val ∈ G.edgeSet ↔ cfg e = true := cfg_mem_iff cfg e
        classical
        have hmem : (↑e ∈ (graphOfCfg cfg).edgeSet) ↔ cfg e = true := by
          simpa [hG] using h_iff

        by_cases h : cfg e = true
        · simp [h, hmem]      -- both sides reduce to `p`
        · simp [h, hmem]      -- both sides reduce to `1 - p`
    have h_sum_products :
        (Finset.univ : Finset (Edge → Bool)).sum
            (fun cfg => ENNReal.ofReal (graphProbabilityProduct' (graphOfCfg cfg) p)) =
        (Finset.univ : Finset (Edge → Bool)).sum
            (fun cfg => ENNReal.ofReal
              (∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
                (if cfg e = true then p else (1 - p)))) := by
      refine Finset.sum_congr rfl ?_
      intro cfg _
      simp [h_product_rewrite]
    have h_nonneg :
        ∀ cfg : Edge → Bool,
          0 ≤ ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
          (if cfg e = true then p else (1 - p)) := by
      intro cfg
      refine Finset.prod_nonneg ?_
      intro e _
      by_cases hcfg : cfg e = true
      · simpa [hcfg] using hp_nonneg
      · have : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
        simpa [hcfg] using this
    have h_ofReal_sum :
        (Finset.univ : Finset (Edge → Bool)).sum
            (fun cfg => ENNReal.ofReal
            (∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
            (if cfg e = true then p else (1 - p)))) =
        ENNReal.ofReal (∑ cfg : Edge → Bool,
        ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
        (if cfg e = true then p else (1 - p))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro cfg _
      exact h_nonneg cfg
    -- "key" combinatorial identity, summing over graph probabilities for all allowed graphs
    -- on `E` gives a finite product of `1`s
    have h_factorization :
        (∑ cfg : Edge → Bool,
            ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
              (if cfg e = true then p else (1 - p))) =
        ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
        (p + (1 - p)) := by
      classical
      have h_sum :
          (∑ cfg : Edge → Bool,
              ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
              (if cfg e = true then p else (1 - p))) =
          ∑ cfg ∈ Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)),
              ∏ e : Edge, (if cfg e = true then p else (1 - p)) := by
        have h_pi :
            Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)) =
              (Finset.univ : Finset (Edge → Bool)) := by
          ext cfg
          simp [Fintype.mem_piFinset]
        have h_attach :
            ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach =
              (Finset.univ : Finset Edge) := by
          ext e
          simp [Edge]
        calc
          (∑ cfg : Edge → Bool,
              ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
                (if cfg e = true then p else (1 - p)))
              =
                ∑ cfg : Edge → Bool,
                  ∏ e ∈ (Finset.univ : Finset Edge), (if cfg e = true then p else (1 - p)) := by
                    congr 1
                    ext cfg
                    rw [h_attach]
          _ =
              ∑ cfg ∈ (Finset.univ : Finset (Edge → Bool)),
                ∏ e ∈ (Finset.univ : Finset Edge), (if cfg e = true then p else (1 - p)) := by
                  simp
          _ =
              ∑ cfg ∈ Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)),
                ∏ e ∈ (Finset.univ : Finset Edge), (if cfg e = true then p else (1 - p)) := by
                  rw [← h_pi]
          _ =
              ∑ cfg ∈ Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)),
                ∏ e : Edge, (if cfg e = true then p else (1 - p)) := by
                  simp
      -- sum-prod swap
      have h_prod_sum :
          ∑ cfg ∈ Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)),
              ∏ e : Edge, (if cfg e = true then p else (1 - p)) =
          ∏ e : Edge, ∑ b ∈ (Finset.univ : Finset Bool), (if b = true then p else (1 - p)) := by
        simpa using
          (Finset.sum_prod_piFinset
            (κ := Bool)
            (ι := Edge)
            (s := (Finset.univ : Finset Bool))
            (g := fun _ b => if b = true then p else (1 - p)))
      have h_bool :
          ∏ e : Edge, ∑ b ∈ (Finset.univ : Finset Bool), (if b = true then p else (1 - p)) =
          ∏ e : Edge, (p + (1 - p)) := by
        simp
      refine (h_sum.trans (h_prod_sum.trans h_bool)).trans ?_
      simp -- End `have h_factorization`

    calc
      (Finset.univ : Finset (SimpleGraph E)).sum
            (fun G => ENNReal.ofReal (graphProbabilityProduct' G p))
          = (Finset.univ : Finset (Edge → Bool)).sum
              (fun cfg => ENNReal.ofReal (graphProbabilityProduct' (graphOfCfg cfg) p)) :=
              h_sum_reindex
      _ = (Finset.univ : Finset (Edge → Bool)).sum
              (fun cfg => ENNReal.ofReal
                (∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
                  (if cfg e = true then p else (1 - p)))) :=
            h_sum_products
      _ = ENNReal.ofReal (∑ cfg : Edge → Bool,
        ∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag).attach,
          (if cfg e = true then p else (1 - p))) :=
            h_ofReal_sum
      _ = ENNReal.ofReal (∏ e ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag),
        (p + (1 - p))) := by
            simpa using congrArg ENNReal.ofReal h_factorization

  -- Step 2: Simplify (p + (1-p))^k = 1^k = 1
  have step2_simplify :
      ENNReal.ofReal (∏ _pair ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag),
        (((Fintype.card E : ℕ) : ℝ) ^ (-α) + (1 - ((Fintype.card E : ℕ) : ℝ) ^ (-α)))) = 1 := by
    set p := ((Fintype.card E : ℕ) : ℝ) ^ (-α)
    have h_add : p + (1 - p) = 1 := by ring
    simp [h_add, Finset.prod_const_one]

  -- Combine steps


  have h_measure :
      (measureOf' (E := E) α) Set.univ =
        (Finset.univ : Finset (SimpleGraph E)).sum
          (fun G => ENNReal.ofReal
            (graphProbabilityProduct' G (((Fintype.card E : ℕ) : ℝ) ^ (-α)))) := by
    simp [measureOf']

  calc (measureOf' (E := E) α) Set.univ
      = (Finset.univ : Finset (SimpleGraph E)).sum
          (fun G => ENNReal.ofReal (graphProbabilityProduct' G (((Fintype.card E : ℕ) : ℝ) ^ (-α))))
          := h_measure
    _ = ENNReal.ofReal (∏ _pair ∈ ((Finset.univ : Finset E).sym2 \ Finset.univ.image Sym2.diag),
          (((Fintype.card E : ℕ) : ℝ) ^ (-α) + (1 - ((Fintype.card E : ℝ) : ℝ) ^ (-α))))
          := step1_apply_prod_add
    _ = 1 := step2_simplify

end ShelahSpencer
#min_imports
