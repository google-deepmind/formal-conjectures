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

import FormalConjectures.Util.ProblemImports

/-!
# Hadwiger's conjecture

Hadwiger's conjecture states that every graph with a chromatic number of at least $k$ contains a
complete graph on $k$ vertices as a minor. This is a generalization of the four color theorem,
which states that every planar graph can be colored with at most four colors.

*References:*

- [Hadwiger's conjecture](https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory))
-/


open Classical

/--
A `SimpleGraph'` has vertices `verts` which is a subset of some type `V`, and
the condition that if two vertices are adjacent, `Adj u v`, then both are in
the vertex set.
-/
structure SimpleGraph' (V : Type*) where
  verts : Set V
  Adj : V → V → Prop
  left_mem_verts_of_adj : ∀ (u v : V), Adj u v → u ∈ verts
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph

variable {V : Type*}

/--
New graph obtained by deleting some vertices, and any edges through them.
-/
def SimpleGraph'.deleteVerts (G : SimpleGraph' V) (s : Set V) : SimpleGraph' V where
  verts := G.verts \ s
  Adj u v := G.Adj u v ∧ u ∉ s ∧ v ∉ s
  Adj_of_verts u v h :=
    ⟨⟨(G.Adj_of_verts u v h.1).1, h.2.1⟩, ⟨(G.Adj_of_verts u v h.1).2, h.2.2⟩⟩
  symm _ _ h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless v h := G.loopless v h.1

/--
New graph obtained by deleting a given set of edges.
-/
def SimpleGraph'.deleteEdges (G : SimpleGraph' V) (s : Set (Sym2 V)) :
    SimpleGraph' V where
  verts := G.verts
  Adj u v := G.Adj u v ∧ s(u, v) ∉ s
  Adj_of_verts u v h := by
    by_cases h_case : s(u, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte] at h
      exact G.Adj_of_verts u v h
  symm u v h := by
    by_cases h_case : s(u, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte, if_false_left] at h ⊢
      have h_case' : s(v, u) ∉ s := by rwa [Sym2.eq_swap]
      simp only [h_case', not_false_eq_true, true_and]
      exact G.symm h
  loopless v h := by
    by_cases h_case : s(v, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte] at h
      exact G.loopless v h

def SimpleGraph'.edgeSet (G : SimpleGraph' V) : Set (Sym2 V) :=
  {e | Sym2.lift ⟨(G.Adj · ·), sorry⟩ e}

@[category API]
lemma SimpleGraph'.mem_edgeSet (G : SimpleGraph' V) {e : Sym2 V} :
    e ∈ G.edgeSet ↔ ∃ u v, s(u, v) = e ∧ G.Adj u v := by
  simp [SimpleGraph'.edgeSet]

/--
New graph obtained by contracting an edge `e` in the original `edgeSet`. To create this graph,
delete a `choice` of one end of `e` from the vertex set, and reroute any free edges to the other
end of `e`.
-/
def SimpleGraph'.contractEdge (G : SimpleGraph' V) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    SimpleGraph' V where
  verts := G.verts \ {(Quot.out e).1}
  Adj u v :=
    u ≠ v ∧ u ≠ (Quot.out e).1 ∧ v ≠ (Quot.out e).1 ∧ (G.Adj u v ∨
     (u = (Quot.out e).2 ∧ G.Adj (Quot.out e).1 v) ∨
     (v = (Quot.out e).2 ∧ G.Adj u (Quot.out e).1))
  Adj_of_verts u v h := by
    simp only [ne_eq] at h
    obtain ⟨u_ne_v, hadj⟩ := h
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · -- Show u ∈ G.verts \ {(Quot.out e).1}
      refine ⟨?_, hadj.1⟩
      cases hadj.2.2 with
      | inl h => exact (G.Adj_of_verts u v h).1
      | inr h =>
        cases h with
        | inl h =>
          rw [SimpleGraph'.mem_edgeSet] at he
          obtain ⟨u₁, v₁, s_eq_e, adj₁⟩ := he
          have : e = s((Quot.out e).1, (Quot.out e).2) := by exact (Quot.out_eq e).symm
          rw [this, Sym2.eq_iff] at s_eq_e
          have := G.Adj_of_verts u₁ v₁ adj₁
          cases s_eq_e with
          | inl hh => convert this.2
                      exact h.1.trans hh.2.symm
          | inr hh => convert this.1
                      exact h.1.trans hh.1.symm
        | inr h => exact (G.Adj_of_verts u _ h.2).1
    · refine ⟨?_, hadj.2.1⟩
      cases hadj.2.2 with
      | inl h => exact (G.Adj_of_verts u v h).2
      | inr h =>
        cases h with
        | inl h => exact (G.Adj_of_verts _ v h.2).2
        | inr h =>
          rw [SimpleGraph'.mem_edgeSet] at he
          obtain ⟨u₁, v₁, s_eq_e, adj₁⟩ := he
          have : e = s((Quot.out e).1, (Quot.out e).2) := by exact (Quot.out_eq e).symm
          rw [this, Sym2.eq_iff] at s_eq_e
          have := G.Adj_of_verts u₁ v₁ adj₁
          cases s_eq_e with
          | inl hh => convert this.2
                      exact h.1.trans hh.2.symm
          | inr hh => convert this.1
                      exact h.1.trans hh.1.symm
  symm qu qv h := by
    simp only [ne_eq] at h ⊢
    refine ⟨Ne.symm h.1, h.2.2.1, h.2.1, ?_⟩
    cases h.2.2.2 with
    | inl h => left; exact G.symm h
    | inr h => right; cases h with
      | inl h => right; exact ⟨h.1, G.symm h.2⟩
      | inr h => left; exact ⟨h.1, G.symm h.2⟩

/--
Now we can define graph minors: keep the same ambient vertex type, but
inductively delete edges, vertices, or contract an edge.
-/
inductive SimpleGraph'.Minor : SimpleGraph' V → SimpleGraph' V → Prop
| refl (G : SimpleGraph' V) : G.Minor G
| delete_edge {G H : SimpleGraph' V} (e : Sym2 V) :
    H.Minor G → H.Minor (G.deleteEdges {e})
| delete_vertex {G H : SimpleGraph' V} (v : V) :
    H.Minor (G.deleteVerts {v}) → H.Minor G
| contract_edge {G H : SimpleGraph' V} (e : Sym2 V) (he : e ∈ G.edgeSet) :
    H.Minor (G.contractEdge he) → H.Minor G




#exit

import Mathlib

variable {V : Type*}

-- First, define the equivalence relation for contracting edge e
def SimpleGraph.contractEdgeRel (e : Sym2 V) : V → V → Prop :=
  fun u v => u = v ∨ s(u, v) = e

-- Then define the setoid instance
def SimpleGraph.contractEdgeSetoid (e : Sym2 V) : Setoid V :=
{ r := contractEdgeRel e,
  iseqv := {
    refl x := by left; rfl
    symm h := by
      cases h with
      | inl hh => left; exact hh.symm
      | inr hh => right; rw [← hh, Sym2.eq_swap]
    trans exy eyz := by
      cases exy with
      | inl hxy => rwa [hxy]
      | inr hxy =>
        cases eyz with
        | inl hyz => right; rwa [hyz] at hxy
        | inr hzy =>
          cases Sym2.eq_iff.mp (hxy.trans hzy.symm) with
          | inl h => right; rwa [← h.1] at hzy
          | inr h => left; exact h.1
  } }

-- And now you can define what it means to contract an edge, on the type `V / ⟨e⟩`
def SimpleGraph.contractEdge (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph (Quotient (contractEdgeSetoid e)) where
  Adj qu qv :=
    qu ≠ qv ∧
    Quotient.liftOn₂ qu qv
      (fun u v => G.Adj u v)
      (fun u₁ u₂ v₁ v₂ hu hv => by sorry)
  symm := by sorry

#exit

section NewSimpleGraph

structure SimpleGraph' (V : Type*) where
  verts : Set V
  Adj : V → V → Prop
  Adj_of_verts : ∀ (u v : V), Adj u v → u ∈ verts ∧ v ∈ verts
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph

end NewSimpleGraph

variable {V : Type*}

--#check SimpleGraph.deleteEdges
section DeleteEdges

open Classical

def SimpleGraph'.deleteEdges (G : SimpleGraph' V) (s : Set (Sym2 V)) : SimpleGraph' V where
  verts := G.verts
  Adj u v := if s(u, v) ∈ s then False else G.Adj u v
  Adj_of_verts u v h := by
    by_cases h_case : s(u, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte] at h
      exact G.Adj_of_verts u v h
  symm u v h := by
    by_cases h_case : s(u, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte, if_false_left] at h ⊢
      have h_case' : s(v, u) ∉ s := by rwa [Sym2.eq_swap]
      simp only [h_case', not_false_eq_true, true_and]
      exact G.symm h
  loopless v h := by
    by_cases h_case : s(v, v) ∈ s
    · simp [h_case] at h
    · simp only [h_case, ↓reduceIte] at h
      exact G.loopless v h

end DeleteEdges

def SimpleGraph'.edgeSet (G : SimpleGraph' V) : Set (Sym2 V) :=
  {e | ∃ u v, s(u, v) = e ∧ G.Adj u v}

@[category API]
lemma SimpleGraph'.mem_edgeSet (G : SimpleGraph' V) {e : Sym2 V} :
    e ∈ G.edgeSet ↔ ∃ u v, s(u, v) = e ∧ G.Adj u v := by
  simp [SimpleGraph'.edgeSet]

section ContractEdge

def SimpleGraph'.contractEdge (G : SimpleGraph' V) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    SimpleGraph' V where
  verts := G.verts \ {(Quot.out e).1}
  Adj u v :=
    u ≠ v ∧
    u ≠ (Quot.out e).1 ∧
    v ≠ (Quot.out e).1 ∧
    (G.Adj u v ∨
     (u = (Quot.out e).2 ∧ G.Adj (Quot.out e).1 v) ∨
     (v = (Quot.out e).2 ∧ G.Adj u (Quot.out e).1))
  Adj_of_verts u v h := by
    simp only [ne_eq] at h
    obtain ⟨u_ne_v, hadj⟩ := h
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · -- Show u ∈ G.verts \ {(Quot.out e).1}
        refine ⟨?_, hadj.1⟩
        cases hadj.2.2 with
        | inl h => exact (G.Adj_of_verts u v h).1
        | inr h =>
            cases h with
            | inl h =>
                rw [SimpleGraph'.mem_edgeSet] at he
                obtain ⟨u₁, v₁, s_eq_e, adj₁⟩ := he
                have : e = s((Quot.out e).1, (Quot.out e).2) := by exact (Quot.out_eq e).symm
                rw [this, Sym2.eq_iff] at s_eq_e
                have := G.Adj_of_verts u₁ v₁ adj₁
                cases s_eq_e with
                | inl hh => convert this.2
                            exact h.1.trans hh.2.symm
                | inr hh => convert this.1
                            exact h.1.trans hh.1.symm
            | inr h => exact (G.Adj_of_verts u _ h.2).1
    ·   refine ⟨?_, hadj.2.1⟩
        cases hadj.2.2 with
        | inl h => exact (G.Adj_of_verts u v h).2
        | inr h =>
            cases h with
            | inl h => exact (G.Adj_of_verts _ v h.2).2
            | inr h =>
                rw [SimpleGraph'.mem_edgeSet] at he
                obtain ⟨u₁, v₁, s_eq_e, adj₁⟩ := he
                have : e = s((Quot.out e).1, (Quot.out e).2) := by exact (Quot.out_eq e).symm
                rw [this, Sym2.eq_iff] at s_eq_e
                have := G.Adj_of_verts u₁ v₁ adj₁
                cases s_eq_e with
                | inl hh => convert this.2
                            exact h.1.trans hh.2.symm
                | inr hh => convert this.1
                            exact h.1.trans hh.1.symm
  symm qu qv h := by
    simp only [ne_eq] at h ⊢
    refine ⟨Ne.symm h.1, h.2.2.1, h.2.1, ?_⟩
    cases h.2.2.2 with
    | inl h => left; exact G.symm h
    | inr h => right; cases h with
        | inl h => right; exact ⟨h.1, G.symm h.2⟩
        | inr h => left; exact ⟨h.1, G.symm h.2⟩


end ContractEdge

section DeleteVertex

def SimpleGraph'.deleteVerts (G : SimpleGraph' V) (s : Set V) : SimpleGraph' V where
  verts := G.verts \ s
  Adj u v := G.Adj u v ∧ u ∉ s ∧ v ∉ s
  Adj_of_verts u v h :=
    ⟨⟨(G.Adj_of_verts u v h.1).1, h.2.1⟩, ⟨(G.Adj_of_verts u v h.1).2, h.2.2⟩⟩
  symm _ _ h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless v h := G.loopless v h.1

end DeleteVertex

variable {W : Type*}

inductive SimpleGraph'.Minor : SimpleGraph' V → SimpleGraph' V → Prop
| refl (G : SimpleGraph' V) : G.Minor G
| delete_edge {G H : SimpleGraph' V} (e : Sym2 V) :
    H.Minor G → H.Minor (G.deleteEdges {e})
| delete_vertex {G H : SimpleGraph' V} (v : V) :
    H.Minor (G.deleteVerts {v}) → H.Minor G
| contract_edge {G H : SimpleGraph' V} (e : Sym2 V) (he : e ∈ G.edgeSet) :
    H.Minor (G.contractEdge he) → H.Minor G

























    #exit
                    | mk hu_eq h_adj =>
                    rw [hu_eq]
                    -- Now we need to show (Quot.out e).2 ∈ G.verts
                    -- Since e ∈ G.edgeSet, we have some adjacency involving e
                    have e_exists : ∃ x y, s(x, y) = e ∧ G.Adj x y := by
                        exact he  -- assuming edgeSet is defined this way
                    cases e_exists with
                    | mk x hx =>
                        cases hx with
                        | mk y hxy =>
                        cases hxy with
                        | mk e_eq adj_xy =>
                            -- We have s(x, y) = e and G.Adj x y
                            -- By Quot.out properties, (Quot.out e).1 and (Quot.out e).2 should be x and y (in some order)
                            have : (Quot.out e).1 = x ∧ (Quot.out e).2 = y ∨ (Quot.out e).1 = y ∧ (Quot.out e).2 = x := by
                            sorry -- This needs a lemma about Quot.out and s(x,y)
                            cases this with
                            | inl h_case =>
                            rw [h_case.2]
                            exact (G.Adj_of_verts x y adj_xy).2
                            | inr h_case =>
                            rw [h_case.2]
                            exact (G.Adj_of_verts x y adj_xy).1
      sorry
    sorry
#exit
            cases hadj with
            | inl h_orig =>
            exact (G.Adj_of_verts u v h_orig).1
            | inr h_redirect =>
            cases h_redirect with
            | inl ⟨hu_eq, h_adj⟩ =>
                rw [hu_eq]
                exact (G.Adj_of_verts (Quot.out e).1 v h_adj).2
            | inr ⟨hv_eq, h_adj⟩ =>
                exact (G.Adj_of_verts u (Quot.out e).1 h_adj).1
    · -- Show u ≠ (Quot.out e).1
    cases h with
    | mk hne hadj =>
        intro hu_eq
        cases hadj with
        | inl h_orig =>
        rw [hu_eq] at h_orig
        -- We have G.Adj (Quot.out e).1 v, so v ∈ G.verts
        -- But we also have u ≠ v, so (Quot.out e).1 ≠ v
        -- This should be fine unless v = (Quot.out e).1, but then we'd have a contradiction
        sorry
        | inr h_redirect =>
        cases h_redirect with
        | inl ⟨hu_eq_snd, h_adj⟩ =>
            -- We have u = (Quot.out e).2 and u = (Quot.out e).1
            -- So (Quot.out e).1 = (Quot.out e).2, which contradicts e being a proper edge
            rw [hu_eq] at hu_eq_snd
            -- Need lemma that (Quot.out e).1 ≠ (Quot.out e).2
            sorry
        | inr ⟨hv_eq, h_adj⟩ =>
            rw [hu_eq] at h_adj
            exact G.loopless (Quot.out e).1 h_adj
    · -- Show v ∈ G.verts \ {(Quot.out e).1} (similar proof)
        simp only [Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · -- Show v ∈ G.verts
        cases h with
        | mk hne hadj =>
            cases hadj with
            | inl h_orig =>
            exact (G.Adj_of_verts u v h_orig).2
            | inr h_redirect =>
            cases h_redirect with
            | inl ⟨hu_eq, h_adj⟩ =>
                exact (G.Adj_of_verts (Quot.out e).1 v h_adj).2
            | inr ⟨hv_eq, h_adj⟩ =>
                rw [hv_eq]
                exact (G.Adj_of_verts u (Quot.out e).1 h_adj).2
        · -- Show v ≠ (Quot.out e).1
        cases h with
        | mk hne hadj =>
            intro hv_eq
            cases hadj with
            | inl h_orig =>
            rw [hv_eq] at h_orig
            -- Similar to above case
            sorry
            | inr h_redirect =>
            cases h_redirect with
            | inl ⟨hu_eq, h_adj⟩ =>
                rw [hv_eq] at h_adj
                exact G.loopless (Quot.out e).1 (G.symm h_adj)
            | inr ⟨hv_eq_snd, h_adj⟩ =>
                rw [hv_eq] at hv_eq_snd
                -- Again, (Quot.out e).1 = (Quot.out e).2 contradiction
                sorry

#exit
def SimpleGraph'.contractEdge (G : SimpleGraph' V) (e : Sym2 V) : SimpleGraph' V where
  verts := G.verts \ {(Quot.out e).1} -- Remove one endpoint
  Adj u v :=
    u ≠ v ∧
    (G.Adj u v ∨  -- Original adjacency
     (u = (Quot.out e).2 ∧ G.Adj (Quot.out e).1 v) ∨  -- Redirect from removed vertex
     (v = (Quot.out e).2 ∧ G.Adj u (Quot.out e).1))   -- Redirect to removed vertex
  Adj_of_verts u v h := by

end ContractEdge
#exit
-- First, define the equivalence relation for contracting edge e
def SimpleGraph'.contractEdgeRel (e : Sym2 V) : V → V → Prop :=
  fun u v => u = v ∨ s(u, v) = e

-- Then define the setoid instance
def SimpleGraph'.contractEdgeSetoid (e : Sym2 V) : Setoid V :=
{ r := contractEdgeRel e,
  iseqv := {
    refl x := by left; rfl
    symm h := by
      cases h with
      | inl hh => left; exact hh.symm
      | inr hh => right; rw [← hh, Sym2.eq_swap]
    trans exy eyz := by
      cases exy with
      | inl hxy => rwa [hxy]
      | inr hxy =>
        cases eyz with
        | inl hyz => right; rwa [hyz] at hxy
        | inr hzy =>
          cases Sym2.eq_iff.mp (hxy.trans hzy.symm) with
          | inl h => right; rwa [← h.1] at hzy
          | inr h => left; exact h.1
  } }

def SimpleGraph'.contractEdge (G : SimpleGraph' V) (e : Sym2 V) :
    SimpleGraph' (Quotient (contractEdgeSetoid e)) where
  verts := {⟦v⟧ | v ∈ G.verts}
  Adj qu qv :=
    qu ≠ qv ∧
    Quotient.liftOn₂ qu qv
      (fun u v => G.Adj u v)
      (fun u₁ u₂ v₁ v₂ hu hv => by
        -- Well-definedness proof
        simp only [eq_iff_iff]
        -- Need to show: G.Adj u₁ v₁ ↔ G.Adj u₂ v₂ when u₁ ~ u₂ and v₁ ~ v₂
        sorry)
  Adj_of_verts qu qv h := by
    sorry
  symm qu qv h := by
    sorry
    -- -- cases h with
    -- -- | mk hne hadj =>
    -- --   constructor
    -- --   · exact hne.symm
    -- --   · apply Quotient.inductionOn₂ qu qv
    -- --     intros u v
    -- --     simp at hadj ⊢
    --     exact G.symm hadj
  loopless qv h := by
    sorry
    -- cases h with
    -- | mk hne _ =>
    --   exact hne rfl

end ContractEdge

#exit

V \ ⟨e⟩

def SimpleGraph.contractEdge (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph (Quotient (contractEdgeSetoid e)) :=
{ Adj qu qv := Quotient.liftOn₂ qu qv
    (fun u v => G.Adj u v ∧ ¬(contractEdgeRel e u v ∧ u ≠ v))
    (fun a₁ a₂ b₁ b₂ ha hb ↦ by
      congr 1
      sorry
      sorry),
  symm qu qv h := by
    sorry
    -- apply Quotient.inductionOn₂ qu qv
    -- intros u v h
    -- simp at h ⊢
    -- exact ⟨G.symm h.1, fun ⟨hrel, hne⟩ => h.2 ⟨by
    --   cases hrel with
    --   | inl h => left; exact h.symm
    --   | inr h => right; rwa [Sym2.eq_swap], hne.symm⟩⟩,
  loopless qv h := by
    sorry
}
    -- apply Quotient.inductionOn qv
    -- intro v h
    -- simp at h
    -- cases h with
    -- | mk h_adj h_not_rel =>
    --   exfalso
    --   apply h_not_rel
    --   exact ⟨Left.intro rfl, fun h_eq => G.loopless v h_adj⟩ }

end ContractEdge

def SimpleGraph.deleteVert (G : SimpleGraph V) (v : V) : SimpleGraph {w // w ≠ v} := sorry

variable {W : Type*}

inductive SimpleGraph.Minor : SimpleGraph W → SimpleGraph V → Prop
| refl (G : SimpleGraph V) : G.Minor G
| delete_edge {G H : SimpleGraph V} (e : Sym2 V) :
    H.Minor G → H.Minor (G.deleteEdges {e})
| delete_vertex {G : SimpleGraph V} {H : SimpleGraph W} (v : V) :
    sorry --H.Minor (G.deleteVert v) → H.Minor G
| contract_edge {G : SimpleGraph V} {H : SimpleGraph W} (e : Sym2 V) (he : e ∈ G.edgeSet) :
    H.Minor (G.contractEdge e) → H.Minor G


theorem Minor.trans {G H K : SimpleGraph V} :
        G.Minor H → H.Minor K → G.Minor K := by
    sorry

theorem subgraph_minor {G H : SimpleGraph V} :
        G ≤ H → G.Minor H := by
    sorry

theorem complete_graph_minor_iff_clique (k : ℕ) (G : SimpleGraph V) :
    (completeGraph (Fin k)).Minor G ↔
        ∃ (S : Finset V), S.card = k ∧ G.IsClique S := by
    sorry

@[category research open, AMS 05]
theorem hadwiger_weaker (G : SimpleGraph V) (k : ℕ)
    (h : k ≤ G.chromaticNumber) : Nonempty (SimpleGraph.Embedding (completeGraph (Fin k)) G) := by
  sorry

def hasCompleteMinor (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k → Set V),
    (∀ i j, i ≠ j → ∃ u ∈ f i, ∃ v ∈ f j, G.Adj u v) ∧
    (∀ i, (f i).Nonempty ∧ G.Connected (G.induce (f i)))
