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

public import Mathlib

/-!
# Strong edge colourings and the strong chromatic index

Two edges of `G` are *strongly independent* if no endpoint of one equals or is adjacent to an
endpoint of the other. A *strong edge colouring* colours the edges so that any two distinct
edges of the same colour are strongly independent. The *strong chromatic index* `sq(G)` is the
least number of colours in a strong edge colouring.

## Main results

* `SimpleGraph.strongChromaticIndex_le_card_edgeSet`: $sq(G) \le |E(G)|$.
* `SimpleGraph.strongChromaticIndex_eq_card_of_forall_not_stronglyIndependent`: if no two
  distinct edges are strongly independent, then $sq(G) = |E(G)|$.
* `SimpleGraph.strongChromaticIndex_le_two_mul_sq`: the greedy bound
  $sq(G) \le 2\Delta^2 - 2\Delta + 1$.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Two edges `e` and `f` (given as unordered pairs) are *strongly independent* in `G` if no
endpoint of `e` equals or is adjacent to an endpoint of `f`. -/
def StronglyIndependent (e f : Sym2 V) : Prop :=
  ∀ u ∈ e, ∀ v ∈ f, u ≠ v ∧ ¬ G.Adj u v

/-- A colouring of the edges of `G` with `k` colours is a *strong edge colouring* if any two
distinct edges of the same colour are strongly independent. Equivalently, each colour class
induces a union of vertex-disjoint edges. -/
def IsStrongEdgeColoring {k : ℕ} (c : G.edgeSet → Fin k) : Prop :=
  ∀ e f : G.edgeSet, e ≠ f → c e = c f → G.StronglyIndependent e.1 f.1

/-- The *strong chromatic index* `sq(G)`: the least number of colours in a strong edge
colouring of `G`. -/
noncomputable def strongChromaticIndex : ℕ :=
  sInf {k : ℕ | ∃ c : G.edgeSet → Fin k, G.IsStrongEdgeColoring c}

lemma StronglyIndependent.symm {G : SimpleGraph V} {e f : Sym2 V}
    (h : G.StronglyIndependent e f) : G.StronglyIndependent f e := by
  intro u hu v hv
  obtain ⟨h1, h2⟩ := h v hv u hu
  exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩

lemma strongChromaticIndex_le_of_coloring {k : ℕ} (c : G.edgeSet → Fin k)
    (hc : G.IsStrongEdgeColoring c) : G.strongChromaticIndex ≤ k :=
  Nat.sInf_le ⟨c, hc⟩

/-- An injective colouring is always strong, so `sq(G) ≤ |E(G)|`. -/
lemma strongChromaticIndex_le_card_edgeSet [Fintype G.edgeSet] :
    G.strongChromaticIndex ≤ Fintype.card G.edgeSet := by
  let c : G.edgeSet → Fin (Fintype.card G.edgeSet) := Fintype.equivFin _
  refine G.strongChromaticIndex_le_of_coloring c ?_
  intro e f hef hc
  exact absurd ((Fintype.equivFin _).injective hc) hef

lemma exists_strongEdgeColoring [Fintype G.edgeSet] :
    ∃ c : G.edgeSet → Fin G.strongChromaticIndex, G.IsStrongEdgeColoring c := by
  have hne : {k : ℕ | ∃ c : G.edgeSet → Fin k, G.IsStrongEdgeColoring c}.Nonempty := by
    refine ⟨Fintype.card G.edgeSet, Fintype.equivFin _, ?_⟩
    intro e f hef hc
    exact absurd ((Fintype.equivFin _).injective hc) hef
  exact Nat.sInf_mem hne

/-- If no two distinct edges of `G` are strongly independent, then `sq(G) = |E(G)|`. -/
lemma strongChromaticIndex_eq_card_of_forall_not_stronglyIndependent [Fintype G.edgeSet]
    (h : ∀ e f : G.edgeSet, e ≠ f → ¬ G.StronglyIndependent e.1 f.1) :
    G.strongChromaticIndex = Fintype.card G.edgeSet := by
  refine le_antisymm G.strongChromaticIndex_le_card_edgeSet ?_
  obtain ⟨c, hc⟩ := G.exists_strongEdgeColoring
  have hinj : Function.Injective c := by
    intro e f hef
    by_contra hne
    exact h e f hne (hc e f hne hef)
  simpa using Fintype.card_le_of_injective c hinj

end SimpleGraph

/-! ### The greedy bound `sq(G) ≤ 2Δ² - 2Δ + 1` -/

namespace SimpleGraph

open scoped Classical in
/-- Greedy colouring: if a symmetric relation has at most `d` "conflicts" at every point, the
points can be coloured with `d + 1` colours so that conflicting points get different colours. -/
lemma exists_coloring_of_conflicts {α : Type*} [Fintype α]
    (R : α → α → Prop) (hR : ∀ a b, R a b → R b a) (d : ℕ)
    (hd : ∀ a, (univ.filter (fun b => b ≠ a ∧ R a b)).card ≤ d) :
    ∃ c : α → Fin (d + 1), ∀ a b, a ≠ b → R a b → c a ≠ c b := by
  have key : ∀ s : Finset α, ∃ c : α → Fin (d + 1),
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → R a b → c a ≠ c b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | insert x s hx ih =>
      obtain ⟨c, hc⟩ := ih
      have hsub : s.filter (fun b => R x b) ⊆ univ.filter (fun b => b ≠ x ∧ R x b) := by
        intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨fun h => hx (h ▸ hb.1), hb.2⟩
      have hlt : ((s.filter (fun b => R x b)).image c).card < (univ : Finset (Fin (d + 1))).card := by
        rw [card_univ, Fintype.card_fin]
        exact Nat.lt_succ_of_le (card_image_le.trans ((card_le_card hsub).trans (hd x)))
      obtain ⟨col, -, hcol⟩ := exists_mem_notMem_of_card_lt_card hlt
      refine ⟨Function.update c x col, ?_⟩
      intro a ha b hb hab hRab
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hx hb)]
        intro h
        exact hcol (mem_image.2 ⟨b, mem_filter.2 ⟨hb, hRab⟩, h.symm⟩)
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hx ha)]
        intro h
        exact hcol (mem_image.2 ⟨a, mem_filter.2 ⟨ha, hR _ _ hRab⟩, h⟩)
      · rw [Function.update_of_ne (by rintro rfl; exact hx ha),
          Function.update_of_ne (by rintro rfl; exact hx hb)]
        exact hc a ha b hb hab hRab
  obtain ⟨c, hc⟩ := key univ
  exact ⟨c, fun a b hab h => hc a (mem_univ _) b (mem_univ _) hab h⟩

open scoped Classical in
/-- For an edge `e = uv`, the number of other edges not strongly independent of `e` is at most
`2Δ² - 2Δ`. -/
lemma card_not_stronglyIndependent_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) :
    (univ.filter (fun f : G.edgeSet => f ≠ e ∧ ¬ G.StronglyIndependent e.1 f.1)).card ≤
      2 * G.maxDegree ^ 2 - 2 * G.maxDegree := by
  classical
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  set D := G.maxDegree
  let T : Finset (Sym2 V) :=
    ((G.incidenceFinset u).erase s(u, v) ∪ (G.incidenceFinset v).erase s(u, v)) ∪
    (((G.neighborFinset u).erase v).biUnion (fun w => (G.incidenceFinset w).erase s(u, w)) ∪
     ((G.neighborFinset v).erase u).biUnion (fun w => (G.incidenceFinset w).erase s(v, w)))
  have hmaps : ∀ f ∈ univ.filter (fun f : G.edgeSet => f ≠ ⟨s(u, v), he⟩ ∧
      ¬ G.StronglyIndependent s(u, v) f.1), f.1 ∈ T := by
    rintro ⟨f, hf⟩ hmem
    simp only [mem_filter, mem_univ, true_and, ne_eq, Subtype.mk.injEq] at hmem
    obtain ⟨hne, hnot⟩ := hmem
    simp only [T, mem_union, mem_erase, mem_biUnion, mem_incidenceFinset, incidenceSet,
      Set.mem_ofPred_eq, mem_neighborFinset]
    by_cases hu : u ∈ f
    · exact Or.inl (Or.inl ⟨hne, hf, hu⟩)
    by_cases hv : v ∈ f
    · exact Or.inl (Or.inr ⟨hne, hf, hv⟩)
    simp only [StronglyIndependent, not_forall, Sym2.mem_iff] at hnot
    obtain ⟨a, ha, b, hb, hab⟩ := hnot
    have hbu : b ≠ u := fun h => hu (h ▸ hb)
    have hbv : b ≠ v := fun h => hv (h ▸ hb)
    rw [not_and_or, not_not, not_not] at hab
    rcases ha with rfl | rfl
    · rcases hab with hab | hab
      · exact absurd hab.symm hbu
      · refine Or.inr (Or.inl ⟨b, ⟨hbv, hab⟩, ?_, hf, hb⟩)
        intro h; exact hu (h ▸ Sym2.mem_mk_left _ _)
    · rcases hab with hab | hab
      · exact absurd hab.symm hbv
      · refine Or.inr (Or.inr ⟨b, ⟨hbu, hab⟩, ?_, hf, hb⟩)
        intro h; exact hv (h ▸ Sym2.mem_mk_left _ _)
  have h1 := card_le_card_of_injOn (fun f : G.edgeSet => f.1) hmaps
    (Subtype.val_injective.injOn)
  refine h1.trans ?_
  have hdeg : ∀ w, G.degree w ≤ D := fun w => G.degree_le_maxDegree w
  have hinc : ∀ w x, G.Adj w x → ((G.incidenceFinset w).erase s(w, x)).card = G.degree w - 1 := by
    intro w x hwx
    rw [card_erase_of_mem, card_incidenceFinset_eq_degree]
    rw [mem_incidenceFinset]
    exact ⟨hwx, Sym2.mem_mk_left _ _⟩
  have hinc' : ∀ w x, G.Adj x w → ((G.incidenceFinset w).erase s(x, w)).card ≤ D - 1 := by
    intro w x hxw
    rw [Sym2.eq_swap, hinc w x hxw.symm]
    exact Nat.sub_le_sub_right (hdeg w) 1
  have hbu : (((G.neighborFinset u).erase v).biUnion
      (fun w => (G.incidenceFinset w).erase s(u, w))).card ≤ (G.degree u - 1) * (D - 1) := by
    refine card_biUnion_le.trans ?_
    have := sum_le_card_nsmul ((G.neighborFinset u).erase v)
      (fun w => ((G.incidenceFinset w).erase s(u, w)).card) (D - 1) (by
        intro w hw
        exact hinc' w u ((G.mem_neighborFinset u w).1 (mem_of_mem_erase hw)))
    rw [card_erase_of_mem ((G.mem_neighborFinset u v).2 huv),
      card_neighborFinset_eq_degree, smul_eq_mul] at this
    exact this
  have hbv : (((G.neighborFinset v).erase u).biUnion
      (fun w => (G.incidenceFinset w).erase s(v, w))).card ≤ (G.degree v - 1) * (D - 1) := by
    refine card_biUnion_le.trans ?_
    have := sum_le_card_nsmul ((G.neighborFinset v).erase u)
      (fun w => ((G.incidenceFinset w).erase s(v, w)).card) (D - 1) (by
        intro w hw
        exact hinc' w v ((G.mem_neighborFinset v w).1 (mem_of_mem_erase hw)))
    rw [card_erase_of_mem ((G.mem_neighborFinset v u).2 huv.symm),
      card_neighborFinset_eq_degree, smul_eq_mul] at this
    exact this
  have hu1 := hinc u v huv
  have hv1 : ((G.incidenceFinset v).erase s(u, v)).card = G.degree v - 1 := by
    rw [Sym2.eq_swap]; exact hinc v u huv.symm
  have hT : T.card ≤ (G.degree u - 1) + (G.degree v - 1) +
      ((G.degree u - 1) * (D - 1) + (G.degree v - 1) * (D - 1)) := by
    refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans ?_)
      ((card_union_le _ _).trans (add_le_add hbu hbv)))
    rw [hu1, hv1]
  refine hT.trans ?_
  have hdu : 1 ≤ G.degree u := G.degree_pos_iff_exists_adj u |>.2 ⟨v, huv⟩
  have hdv : 1 ≤ G.degree v := G.degree_pos_iff_exists_adj v |>.2 ⟨u, huv.symm⟩
  have hDu := hdeg u
  have hDv := hdeg v
  obtain ⟨a, ha⟩ : ∃ a, G.degree u = a + 1 := ⟨_, (Nat.sub_add_cancel hdu).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, G.degree v = b + 1 := ⟨_, (Nat.sub_add_cancel hdv).symm⟩
  obtain ⟨m, hm⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
  have ham : a ≤ m := by omega
  have hbm : b ≤ m := by omega
  rw [ha, hb, hm]
  simp only [Nat.add_sub_cancel]
  have e2 : 2 * (m + 1) ^ 2 - 2 * (m + 1) = 2 * m ^ 2 + 2 * m := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [e2]
  nlinarith

/-- **The greedy bound.** `sq(G) ≤ 2Δ² - 2Δ + 1`. -/
theorem strongChromaticIndex_le_two_mul_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.strongChromaticIndex ≤ 2 * G.maxDegree ^ 2 - 2 * G.maxDegree + 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_coloring_of_conflicts
    (fun e f : G.edgeSet => ¬ G.StronglyIndependent e.1 f.1)
    (fun a b h h' => h h'.symm) _ (fun e => by convert card_not_stronglyIndependent_le G e)
  refine G.strongChromaticIndex_le_of_coloring c ?_
  intro e f hef hcol
  by_contra h
  exact hc e f hef h hcol

end SimpleGraph
