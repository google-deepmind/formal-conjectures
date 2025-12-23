import Mathlib
import FormalConjectures.ForMathlib.Combinatorics.TensorContraction


open scoped TensorProduct
open scoped BigOperators

variable (V : Type*)[NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure TensorNetwork (α β : Type*) [Fintype α] [Fintype β] where
  G : Graph α β
  [loc : ∀ x : α, Fintype (G.incidenceSet x)]
  loopless : ∀ (e : β) (x : α), ¬ G.IsLoopAt e x
  c : ∀ x : α, G.incidenceSet x → Fin (Fintype.card (G.incidenceSet x))
  hc : ∀ x : α, Function.Bijective (c x)

namespace TensorNetwork
noncomputable def deg {α β : Type*} [Fintype α] [Fintype β] (G : TensorNetwork α β) (x : α) : ℕ := by
  have hfin : Fintype (G.G.incidenceSet x) := G.loc x
  exact Fintype.card (G.G.incidenceSet x)
end TensorNetwork

/-- Given a tensor network `G`, the assignement of a tensor `T_v` for each vertex.
Note: we also assigne "junk values for elements of `α` that aren't edges". -/
structure TensorMap {α β : Type*} [Fintype α] [Fintype β] (G : TensorNetwork α β)  where
  tensor : ∀ x : α, ⨂[ℝ]^(G.deg x) V

noncomputable def SingleLegContractionGraph {α β: Type*} [Fintype α] [DecidableEq α] [Fintype β] {G : TensorNetwork α β} (loopless : ∀ (e : β) (x : α), ¬ G.G.IsLoopAt e x) (v w : α) (hv : v ∈ G.G.vertexSet) (hvw : ¬v = w): Graph α β := by
  classical
  refine
    { vertexSet := ?_
      IsLink := ?_
      edgeSet := ?_
      isLink_symm := ?_
      eq_or_eq_of_isLink_of_isLink := ?_
      edge_mem_iff_exists_isLink := ?_
      left_mem_of_isLink := ?_
      }
  . exact G.G.vertexSet \ {w}
  . let is_link_new : β → α → α → Prop := fun e x y =>
      if (w = x) ∨ (w = y) ∨ (x = y) then
        False
      else if (x = v) then
        (G.G.IsLink e v y) ∨ (G.G.IsLink e w y)
      else if (y = v) then
        (G.G.IsLink e x v) ∨ (G.G.IsLink e x w)
      else
        G.G.IsLink e x y
    exact is_link_new
  . exact G.G.edgeSet \ {e | G.G.IsLink e v w}
  . intro e h
    have he : e ∈ G.G.edgeSet := ((Set.mem_diff (s := G.G.edgeSet) (t := {e | G.G.IsLink e v w}) (e : β)).1 h).1
    simp [Symmetric]
    intro x y hwx hwy hxy hexy
    have hsymm := G.G.isLink_symm (e := e) he
    constructor
    . simp [hwx,hwy,Ne.symm hxy]
    . by_cases hyv : y = v
      . simp [hyv]
        by_cases hxv : x = v
        . simp [hxv, hyv] at hexy
          simp [hxv, hexy]
        . simp [hxv,hyv] at hexy
          by_cases hlinkexv : G.G.IsLink e x v
          . simp [hsymm hlinkexv]
          . simp [hlinkexv] at hexy
            simp [hsymm hexy]
      . simp [hyv]
        by_cases hxv : x = v
        . simp [hxv]
          simp [hxv] at hexy
          by_cases hlinkevy : G.G.IsLink e v y
          . simp [hsymm hlinkevy]
          . simp [hlinkevy] at hexy
            simp [hsymm hexy]
        . simp [hxv]
          simp [hxv, hyv] at hexy
          simp [hsymm hexy]
  . intro e x y v_1 w_1 h1 h2
    by_cases hxv1 : x = v_1
    . simp [hxv1]
    . simp [hxv1]
      by_cases hxw1 : x = w_1
      . exact hxw1
      . by_cases hwx : w = x
        . simp [hwx] at h1
        . by_cases hwy : w = y
          . simp [hwy] at h1
          . by_cases hxy : x = y
            . simp [hxy] at h1
            . simp [hwx,hwy,hxy] at h1
              by_cases hwv1 : w = v_1
              . simp [hwv1] at h2
              . simp [hwv1] at h2
                by_cases hww1 : w = w_1
                . simp [hww1] at h2
                . simp [hww1] at h2
                  by_cases hv1w1 : v_1 = w_1
                  . simp [hv1w1] at h2
                  . simp [hv1w1] at h2
                    by_cases hvx : v = x
                    . simp [hvx] at h1
                      simp [hvx] at h2
                      simp [Ne.symm hxv1, Ne.symm hxw1] at h2
                      have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨v_1, w_1, h2⟩
                      have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                      by_cases hlink : G.G.IsLink e x y
                      . apply hG (x := x) (y := y) (v := v_1) (w := w_1) at hlink
                        apply hlink at h2
                        simp [hxv1,hxw1] at h2
                      . simp [hlink] at h1
                        apply hG (x := w) (y := y) (v := v_1) (w := w_1) at h1
                        apply h1 at h2
                        simp [hwv1,hww1] at h2
                    . simp [Ne.symm hvx] at h1
                      by_cases hv1v : v_1 = v
                      . simp [hv1v] at h2
                        by_cases hyv : y = v
                        . simp [hyv] at h1
                          by_cases hlink : G.G.IsLink e x v
                          . have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, v, hlink⟩
                            have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                            by_cases hlink2 : G.G.IsLink e v w_1
                            . apply hG (x := x) (y := v) (v := v) (w := w_1) hlink at hlink2
                              simp [Ne.symm hvx, hxw1] at hlink2
                            . simp [hlink2] at h2
                              apply hG (x := x) (y := v) (v := w) (w := w_1) hlink at h2
                              simp [Ne.symm hwx, hxw1] at h2
                          . simp [hlink] at h1
                            have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, w, h1⟩
                            have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                            by_cases hlink2 : G.G.IsLink e v w_1
                            . apply hG (x := x) (y := w) (v := v) (w := w_1) h1 at hlink2
                              simp [Ne.symm hvx, hxw1] at hlink2
                            . simp [hlink2] at h2
                              apply hG (x := x) (y := w) (v := w) (w := w_1) h1 at h2
                              simp [Ne.symm hwx, hxw1] at h2
                        . simp [hyv] at h1
                          have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, y, h1⟩
                          have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                          by_cases hlink : G.G.IsLink e v w_1
                          . apply hG (x := x) (y := y) (v := v) (w := w_1) h1 at hlink
                            simp [Ne.symm hvx, hxw1] at hlink
                          . simp [hlink] at h2
                            apply hG (x := x) (y := y) (v := w) (w := w_1) h1 at h2
                            simp [Ne.symm hwx, hxw1] at h2
                      . simp [hv1v] at h2
                        by_cases hyv : y = v
                        . simp [hyv] at h1
                          by_cases hw1v : w_1 = v
                          . simp [hw1v] at h2
                            by_cases hlink : G.G.IsLink e x v
                            . have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, v, hlink⟩
                              have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                              by_cases hlink2 : G.G.IsLink e v_1 v
                              . apply hG (x := x) (y := v) (v := v_1) (w := v) hlink at hlink2
                                simp [hxv1, Ne.symm hvx] at hlink2
                              . simp [hlink2] at h2
                                apply hG (x := x) (y := v) (v := v_1) (w := w) hlink at h2
                                simp [hxv1, Ne.symm hwx] at h2
                            . simp [hlink] at h1
                              have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, w, h1⟩
                              have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                              by_cases hlink2 : G.G.IsLink e v_1 v
                              . apply hG (x := x) (y := w) (v := v_1) (w := v) h1 at hlink2
                                simp [hxv1, Ne.symm hvx] at hlink2
                              . simp [hlink2] at h2
                                apply hG (x := x) (y := w) (v := v_1) (w := w) h1 at h2
                                simp [hxv1, Ne.symm hwx] at h2
                          . simp [hw1v] at h2
                            have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨v_1, w_1, h2⟩
                            have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                            by_cases hlink : G.G.IsLink e x v
                            . apply hG (x := x) (y := v) (v := v_1) (w := w_1) hlink at h2
                              simp [hxv1, hxw1] at h2
                            . simp [hlink] at h1
                              apply hG (x := x) (y := w) (v := v_1) (w := w_1) h1 at h2
                              simp [hxv1, hxw1] at h2
                        . simp [hyv] at h1
                          have he := (G.G.edge_mem_iff_exists_isLink e).symm.1 ⟨x, y, h1⟩
                          have hG := G.G.eq_or_eq_of_isLink_of_isLink (e := e)
                          by_cases hw1v : w_1 = v
                          . simp [hw1v] at h2
                            by_cases hlink : G.G.IsLink e v_1 v
                            . apply hG (x := x) (y := y) (v := v_1) (w := v) h1 at hlink
                              simp [hxv1, Ne.symm hvx] at hlink
                            . simp [hlink] at h2
                              apply hG (x := x) (y := y) (v := v_1) (w := w) h1 at h2
                              simp [hxv1, Ne.symm hwx] at h2
                          . simp [hw1v] at h2
                            apply hG (x := x) (y := y) (v := v_1) (w := w_1) h1 at h2
                            simp [hxv1, hxw1] at h2
  . intro e
    constructor
    . intro he
      simp at he
      have he1 := he.1
      have he2 := he.2
      apply (G.G.edge_mem_iff_exists_isLink (e := e)).1 at he1
      rcases he1 with ⟨s, t, hst⟩
      by_cases hsw : s = w
      . use v, t
        simp [Ne.symm hvw]
        simp [hsw] at hst
        apply G.G.isLink_comm.1 at hst
        by_cases htv : t = v
        . simp [htv] at hst
          simp [hst] at he2
        . by_cases hwt : w = t
          . simp [hwt] at hst
            simp [loopless] at hst
          . simp [hwt, Ne.symm htv]
            simp [G.G.isLink_comm.1 hst]
      . by_cases htw : t = w
        . use s, v
          simp [Ne.symm hsw, Ne.symm hvw]
          by_cases hsv : s = v
          . simp [hsv]
            simp [htw,hsv,he2] at hst
          . simp [hsv]
            simp [htw] at hst
            simp [hst]
        . use s, t
          simp [Ne.symm hsw, Ne.symm htw]
          by_cases hst2 : s = t
          . simp [hst2]
            simp [hst2, loopless] at hst
          . simp [hst2]
            by_cases hsv : s = v
            . simp [hsv]
              simp [hsv] at hst
              simp [hst]
            . simp [hsv]
              by_cases htv : t = v
              . simp [htv]
                simp [htv] at hst
                simp [hst]
              . simp [htv, hst]
    . intro h
      rcases h with ⟨s, t, hst⟩
      by_cases hws : w = s
      . simp [hws] at hst
      . by_cases hwt : w = t
        . simp [hwt] at hst
        . by_cases hst2 : s = t
          . simp [hst2] at hst
          . simp [hws, hwt, hst2] at hst
            by_cases hsv : s = v
            . simp [hsv] at hst
              by_cases hlink : G.G.IsLink e v t
              . refine And.intro ?_ ?_
                . exact (G.G.edge_mem_iff_exists_isLink (e := e)).2 ⟨v, t, hlink⟩
                . simp
                  have h := ((G.G.eq_or_eq_of_isLink_of_isLink (e := e) (x := t) (y := v) (v := w) (w := v)) (G.G.isLink_comm.1 hlink))
                  simp [G.G.isLink_comm] at h
                  intro hG
                  simp [hG] at h
                  simp [Ne.symm hwt] at h
                  simp [h] at hlink
                  simp [loopless] at hlink
              . simp [hlink] at hst
                refine And.intro ?_ ?_
                . exact (G.G.edge_mem_iff_exists_isLink (e := e)).2 ⟨w, t, hst⟩
                . simp
                  have h := ((G.G.eq_or_eq_of_isLink_of_isLink (e := e) (x := t) (y := w) (v := v) (w := w)) (G.G.isLink_comm.1 hst))
                  intro hG
                  simp [hG] at h
                  simp [Ne.symm hwt] at h
                  simp [h,hsv] at hst2
            . simp [hsv] at hst
              by_cases htv : t = v
              . simp [htv] at hst
                by_cases hlink : G.G.IsLink e s v
                . refine And.intro ?_ ?_
                  . exact (G.G.edge_mem_iff_exists_isLink (e := e)).2 ⟨s, v, hlink⟩
                  . simp
                    have h := ((G.G.eq_or_eq_of_isLink_of_isLink (e := e) (x := s) (y := v) (v := w) (w := v)) hlink)
                    simp [G.G.isLink_comm] at h
                    intro hG
                    simp [hG] at h
                    simp [Ne.symm hws, hsv] at h
                . simp [hlink] at hst
                  refine And.intro ?_ ?_
                  . exact (G.G.edge_mem_iff_exists_isLink (e := e)).2 ⟨s, w, hst⟩
                  . simp
                    have h := ((G.G.eq_or_eq_of_isLink_of_isLink (e := e) (x := s) (y := w) (v := w) (w := v)) hst)
                    intro hG
                    simp [G.G.isLink_comm] at h
                    simp [hG] at h
                    simp [Ne.symm hws, hsv] at h
              . simp [htv] at hst
                refine And.intro ?_ ?_
                . exact (G.G.edge_mem_iff_exists_isLink (e := e)).2 ⟨s, t, hst⟩
                . simp
                  have h := ((G.G.eq_or_eq_of_isLink_of_isLink (e := e) (x := s) (y := t) (v := v) (w := w)) hst)
                  intro hG
                  simp [hG] at h
                  simp [Ne.symm hws, hsv] at h
  . intro e x y h
    by_cases hwx : w = x
    . simp [hwx] at h
    . by_cases hwy : w = y
      . simp [hwy] at h
      . by_cases hxy : x = y
        . simp [hxy] at h
        . simp [hwx,hwy,hxy] at h
          by_cases hxv : x = v
          . simp [hxv] at hwx
            simp [hxv, hv, Ne.symm hwx]
          . simp [hxv] at h
            by_cases hyv : y = v
            . simp [hyv] at h
              by_cases hlink : G.G.IsLink e x v
              . simp [Ne.symm hwx]
                exact Graph.IsLink.left_mem (h := hlink)
              . simp [hlink] at h
                simp [Ne.symm hwx]
                exact Graph.IsLink.left_mem (h := h)
            . simp [hyv] at h
              simp [Ne.symm hwx]
              exact Graph.IsLink.left_mem (h := h)

noncomputable def SingleLegContractionTensorNetwork {α β: Type*} [Fintype α] [DecidableEq α] [Fintype β] (G : TensorNetwork α β) (loopless : ∀ (e : β) (x : α), ¬ G.G.IsLoopAt e x) (v w : α) (hv : v ∈ G.G.vertexSet) (hvw : ¬v = w):
  TensorNetwork (α := α) (β := β) := by
  classical
  let G' := SingleLegContractionGraph (G := G) (loopless := loopless) (v := v) (w := w) (hv := hv) (hvw := hvw)
  refine
  { G := G'
    loc := ?_         -- the fintype instance field
    loopless := ?_
    c := ?_
    hc := ?_ }
  . intro x
    classical
    infer_instance    -- usually works if β is fintype and IsLink is decidable enough
  . intro e x
    simp [G', SingleLegContractionGraph]
    intro h
    apply Graph.isLink_self_iff.2 at h
    rcases h with ⟨hneq, _⟩
    exact hneq.2.2 rfl
  . intro x
    exact (Fintype.equivFin (G'.incidenceSet x)).1
  . intro x
    exact (Fintype.equivFin (G'.incidenceSet x)).bijective

noncomputable def SingleLegContractionTensorMap {α β: Type*} [Fintype α] [DecidableEq α] [Fintype β] {G : TensorNetwork α β} (T : TensorMap (V := V) G) (loopless : ∀ (e : β) (x : α), ¬ G.G.IsLoopAt e x) (v w : α) (hv : v ∈ G.G.vertexSet) (hvw : ¬v = w):
  TensorMap (V := V) (G := SingleLegContractionTensorNetwork (loopless := loopless) (v := v) (w := w) (hv := hv) (hvw := hvw)):= by
  classical
  let G' := SingleLegContractionTensorNetwork (loopless := loopless) (v := v) (w := w) (hv := hv) (hvw := hvw)
  let E : Set β := { e | e ∈ G.G.edgeSet ∧ G.G.IsLink e v w }
  haveI : Fintype (↑(G.G.incidenceSet v)) := G.loc v
  let φ : (↑E) → ↑(G.G.incidenceSet v) := fun e =>
    ⟨(e : β), by
      have hw : G.G.IsLink (e : β) v w := by simpa [E] using e.2.2
      exact ⟨w, hw⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    simpa [φ] using congrArg Subtype.val hab
  have hcard_le : Fintype.card (↑E) ≤ Fintype.card (↑(G.G.incidenceSet v)) :=
    Fintype.card_le_of_injective φ hφ
  have hcard_le_deg_v : Fintype.card (↑E) ≤ TensorNetwork.deg (G := G) v := by
    -- deg is card of incidenceSet, and hcard_le is already in that form
    simpa [TensorNetwork.deg] using hcard_le

  refine
  {
    tensor := ?_
  }
  . intro x
    by_cases hxw : x = w
    . simp [hxw]
      simp [SingleLegContractionTensorNetwork]
      have hfilter_empty : Finset.filter (fun e => e ∈ (G'.G.incidenceSet w)) Finset.univ = (∅ : Finset β) := by
        ext e
        simp [Graph.incidenceSet]
      simp [hfilter_empty]  -- goal becomes ⊢ ⨂[ℝ]^0 V
      exact 0
    . by_cases hxv : x = v
      . simp [hxv]
        simp [SingleLegContractionTensorNetwork]
        have Tk' : ⨂[ℝ]^(G.deg v) V := by
          simpa [TensorNetwork.deg] using (T.tensor v)
        have Tl' : ⨂[ℝ]^(G.deg w) V := by
          simpa [TensorNetwork.deg] using (T.tensor w)
        let Rel : { e : β // e ∈ G.G.edgeSet ∧ G.G.IsLink e v w } → ℕ × ℕ := fun e =>
          (G.c v ⟨e.1, ⟨w, e.2.2⟩⟩, G.c w ⟨e.1, ⟨v, ((G.G.isLink_symm (e := e) (x := v) (y := w)) e.2.1) e.2.2⟩⟩)
        let R : Set (ℕ × ℕ) := Set.image Rel Set.univ

        have Tvw : ⨂[ℝ]^(G.deg v + G.deg w) V :=
          (TensorContraction (V := V) (k := G.deg v) (l := G.deg w) (m := m) R hR hInjfst hInjsnd f) Tk' Tl'
