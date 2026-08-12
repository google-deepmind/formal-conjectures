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
# Written on the Wall II - Conjecture 438b

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The source conjecture states
`alpha₂(G) ≤ alpha(G) + alpha(G[V \ H₂]) + |E(G[H₂])|`, where
`H₂ = {v | degree v ≤ 2}`.  The proof below establishes the stronger result
for every vertex subset `H`; connectivity and the degree definition of `H₂`
are unnecessary.
-/

namespace WrittenOnTheWallII.GraphConjecture438b

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Edges of `G` whose two endpoints lie in `S`. -/
def internalEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ S

/-- A vertex set is 2-independent when its induced graph has maximum degree
at most one. -/
def IsTwoIndependent (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ v ∈ S, (S.filter fun w => G.Adj v w).card ≤ 1

/-- Internal edges of a 2-independent set are pairwise vertex-disjoint. -/
@[category API, AMS 5]
lemma IsTwoIndependent.internalEdges_pairwise {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} (hS : IsTwoIndependent G S) :
    ∀ e ∈ internalEdges G S, ∀ f ∈ internalEdges G S, e ≠ f →
      Disjoint e.toFinset f.toFinset := by
  classical
  intro e he f hf hef
  rw [Finset.disjoint_left]
  intro x hxe hxf
  rw [Sym2.mem_toFinset, Sym2.mem_iff_exists] at hxe hxf
  obtain ⟨y, rfl⟩ := hxe
  obtain ⟨z, hfEq⟩ := hxf
  have heData := Finset.mem_filter.mp he
  have hfData := Finset.mem_filter.mp hf
  have hxy : G.Adj x y := by simpa using heData.1
  have hxz : G.Adj x z := by simpa [hfEq] using hfData.1
  have hxS : x ∈ S := heData.2 (by simp)
  have hyS : y ∈ S := heData.2 (by simp)
  have hzS : z ∈ S := hfData.2 (by simp [hfEq])
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hef hfEq.symm
  have hpairSub : ({y, z} : Finset V) ⊆ S.filter fun w => G.Adj x w := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [hyS, hzS, hxy, hxz]
  have htwo : 2 ≤ (S.filter fun w => G.Adj x w).card := by
    rw [← Finset.card_pair hyz]
    exact Finset.card_le_card hpairSub
  have hone := hS x hxS
  exact (by omega : False)

/-- Maximum cardinality of an independent subset contained in `B`. -/
noncomputable def indepNumOn (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) : ℕ :=
  by
    classical
    exact (B.powerset.filter fun (A : Finset V) => G.IsIndepSet (A : Set V)).sup card

/-- Maximum cardinality of a 2-independent vertex set. -/
noncomputable def alphaTwo (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  by
    classical
    exact (Finset.univ.powerset.filter fun S => IsTwoIndependent G S).sup card

/-- The source's low-degree layer `H₂`. -/
def lowDegreeLayer (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v ≤ 2

omit [Fintype V] in
lemma IsIndepSet.card_le_indepNumOn {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} (hA : G.IsIndepSet A) (hAB : A ⊆ B) :
    A.card ≤ indepNumOn G B := by
  classical
  unfold indepNumOn
  apply Finset.le_sup
  simp [hAB, hA]

/-- Choice lemma for a pairwise-disjoint family of graph edges.  If every
edge has an endpoint in `D`, one can choose one such endpoint per edge; the
chosen vertices form an independent set when `F` contains every edge among
their ambient vertex set `S`. -/
@[category API, AMS 5]
lemma choose_independent_endpoints (G : SimpleGraph V) [DecidableRel G.Adj]
    (S D : Finset V) (F : Finset (Sym2 V))
    (hF : F ⊆ internalEdges G S)
    (hpair : ∀ e ∈ internalEdges G S, ∀ f ∈ internalEdges G S, e ≠ f →
      Disjoint e.toFinset f.toFinset)
    (hD : ∀ e ∈ F, (e.toFinset ∩ D).Nonempty) :
    ∃ P : Finset V, P ⊆ D ∧ G.IsIndepSet P ∧ P.card = F.card ∧
      ∀ e ∈ F, (P ∩ e.toFinset).Nonempty := by
  classical
  let pick : {e // e ∈ F} → V := fun e => Classical.choose (hD e.1 e.2)
  have hpick_mem (e : {e // e ∈ F}) : pick e ∈ e.1.toFinset ∩ D :=
    Classical.choose_spec (hD e.1 e.2)
  have hinj : Function.Injective pick := by
    intro e f hef
    by_contra hne
    have hd := hpair e.1 (hF e.2) f.1 (hF f.2) (by simpa using hne)
    have hee : pick e ∈ e.1.toFinset := (Finset.mem_inter.mp (hpick_mem e)).1
    have hff : pick f ∈ f.1.toFinset := (Finset.mem_inter.mp (hpick_mem f)).1
    exact (Finset.disjoint_left.1 hd hee (hef ▸ hff))
  let P := Finset.univ.image pick
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_inter.mp (hpick_mem e)).2
  · intro x hx y hy hxy
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hy
    intro hadj
    have heS : pick e ∈ S := by
      have he := hF e.2
      exact (Finset.mem_filter.mp he).2 (Finset.mem_inter.mp (hpick_mem e)).1
    have hfS : pick f ∈ S := by
      have hf := hF f.2
      exact (Finset.mem_filter.mp hf).2 (Finset.mem_inter.mp (hpick_mem f)).1
    let g : Sym2 V := s(pick e, pick f)
    have hg : g ∈ internalEdges G S := by
      simp only [internalEdges, mem_filter, mem_edgeFinset, g]
      refine ⟨hadj, ?_⟩
      intro x hx
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    have he := hF e.2
    have hf := hF f.2
    have hge : g = e.1 := by
      by_contra h
      have hd := hpair e.1 he g hg (Ne.symm h)
      exact (Finset.disjoint_left.1 hd (Finset.mem_inter.mp (hpick_mem e)).1 (by simp [g]))
    have hgf : g = f.1 := by
      by_contra h
      have hd := hpair f.1 hf g hg (Ne.symm h)
      exact (Finset.disjoint_left.1 hd (Finset.mem_inter.mp (hpick_mem f)).1 (by simp [g]))
    exact hxy (congrArg pick (Subtype.ext (hge.symm.trans hgf)))
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  · intro e he
    let es : {e // e ∈ F} := ⟨e, he⟩
    refine ⟨pick es, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨es, Finset.mem_univ _, rfl⟩
    · exact (Finset.mem_inter.mp (hpick_mem es)).1

/-- Strong arbitrary-subset form of WOWII 438b. -/
@[category API, AMS 5]
lemma arbitrary_subset_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V) (hS : IsTwoIndependent G S) :
    S.card ≤ G.indepNum + indepNumOn G (Finset.univ \ H) + (internalEdges G H).card := by
  classical
  let F := internalEdges G S
  let FH := F.filter fun e => e.toFinset ⊆ H
  let FB := F \ FH
  have hpair := hS.internalEdges_pairwise
  have hFall : F ⊆ internalEdges G S := by simp [F]
  have hedge_nonempty (e : Sym2 V) (he : e ∈ F) : e.toFinset.Nonempty := by
    have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have hcard : e.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (by simpa using heG))
    exact Finset.card_pos.mp (by omega)
  have hmeetS : ∀ e ∈ F, (e.toFinset ∩ S).Nonempty := by
    intro e he
    obtain ⟨x, hx⟩ := hedge_nonempty e he
    exact ⟨x, Finset.mem_inter.mpr ⟨hx, (Finset.mem_filter.mp he).2 hx⟩⟩
  obtain ⟨P, hPS, hPind, hPcard, hPcover⟩ :=
    choose_independent_endpoints G S S F hFall hpair hmeetS
  have hAcov : G.IsIndepSet (S \ P : Finset V) := by
    intro x hx y hy hxy hadj
    have hxyEdge : s(x, y) ∈ F := by
      simp only [F, internalEdges, mem_filter, mem_edgeFinset]
      refine ⟨hadj, ?_⟩
      intro z hz
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact (Finset.mem_sdiff.mp hx).1
      · exact (Finset.mem_sdiff.mp hy).1
    have hcovered : x ∈ P ∨ y ∈ P := by
      by_contra hnone
      push_neg at hnone
      have hPe : (P ∩ s(x, y).toFinset).Nonempty := hPcover _ hxyEdge
      obtain ⟨z, hz⟩ := hPe
      have hzP := (Finset.mem_inter.mp hz).1
      have hzxy := (Finset.mem_inter.mp hz).2
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hzxy
      rcases hzxy with rfl | rfl
      · exact hnone.1 hzP
      · exact hnone.2 hzP
    rcases hcovered with hxP | hyP
    · exact (Finset.mem_sdiff.mp hx).2 hxP
    · exact (Finset.mem_sdiff.mp hy).2 hyP
  have hAcard : (S \ P).card ≤ G.indepNum := hAcov.card_le_indepNum
  have hsplitS : S.card = (S \ P).card + P.card := by
    rw [Finset.card_sdiff_add_card_eq_card hPS]
  have hFHsub : FH ⊆ internalEdges G H := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he'.1).1, he'.2⟩
  have hFHcard : FH.card ≤ (internalEdges G H).card := Finset.card_le_card hFHsub
  have hFBsub : FB ⊆ internalEdges G S := by
    intro e he
    exact hFall (Finset.mem_sdiff.mp he).1
  have hmeetB : ∀ e ∈ FB, (e.toFinset ∩ (Finset.univ \ H)).Nonempty := by
    intro e he
    have heF := (Finset.mem_sdiff.mp he).1
    have heNot : ¬ e.toFinset ⊆ H := by
      intro hes
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨heF, hes⟩)
    obtain ⟨x, hxe, hxH⟩ := Finset.not_subset.mp heNot
    exact ⟨x, Finset.mem_inter.mpr ⟨hxe, by simp [hxH]⟩⟩
  obtain ⟨Q, hQB, hQind, hQcard, -⟩ :=
    choose_independent_endpoints G S (Finset.univ \ H) FB hFBsub hpair hmeetB
  have hQbound : FB.card ≤ indepNumOn G (Finset.univ \ H) := by
    rw [← hQcard]
    exact IsIndepSet.card_le_indepNumOn hQind hQB
  have hFsplit : F.card = FH.card + FB.card := by
    have hsub : FH ⊆ F := by
      intro e he
      exact (Finset.mem_filter.mp he).1
    rw [← Finset.card_sdiff_add_card_eq_card hsub]
    simp only [FB]
    omega
  omega

/-- The maximum form of the arbitrary-subset inequality. -/
@[category API, AMS 5]
theorem alphaTwo_arbitrary_subset_bound :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (H : Finset V),
      alphaTwo G ≤ G.indepNum + indepNumOn G (Finset.univ \ H) +
        (internalEdges G H).card := by
  classical
  intro V _ _ G _ H
  unfold alphaTwo
  apply Finset.sup_le
  intro S hS
  exact arbitrary_subset_bound G H S (Finset.mem_filter.mp hS).2

/-- WOWII 438b is true.  The connectivity and order hypotheses are retained
from the source, although the arbitrary-subset theorem above does not need
them. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/Kuberwastaken/c5-k4/blob/e62f2164d91dd83439373dd23fd68479e5407ae5/lean/GraphConjecture438b.lean"]
theorem conjecture438b : answer(True) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      alphaTwo G ≤ G.indepNum +
        indepNumOn G (Finset.univ \ lowDegreeLayer G) +
        (internalEdges G (lowDegreeLayer G)).card := by
  classical
  show True ↔ _
  rw [true_iff]
  intro V _ _ G _ _ _
  exact alphaTwo_arbitrary_subset_bound V G (lowDegreeLayer G)

end WrittenOnTheWallII.GraphConjecture438b
