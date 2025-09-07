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
# Conway's 99-graph problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem)
-/

namespace Conway99Graph

--TODO(firsching): Consider using SimpleGraph.IsSRGWith to formulate the conjecture.
variable {V : Type} {G : SimpleGraph V}
@[category undergraduate, AMS 5]
lemma completeGraphIsClique (s : Finset V) : (⊤ : SimpleGraph V).IsClique s :=
  Pairwise.set_pairwise (fun _ _ a ↦ a) _

variable [Fintype V]

@[category undergraduate, AMS 5]
lemma completeGraph_cliqueSet :
    (⊤ : SimpleGraph V).cliqueSet (Fintype.card V) = {Set.univ.toFinset} := by
  simp only [SimpleGraph.cliqueSet, SimpleGraph.isNClique_iff ⊤, completeGraphIsClique, true_and,
    Set.toFinset_univ]
  exact (Set.Sized.univ_mem_iff fun ⦃x⦄ a ↦ a).mp rfl

variable [DecidableEq V]
/--
Each two non-adjacent vertices have exactly two common neighbors.
-/
def NonEdgesAreDiagonals (G : SimpleGraph V) : Prop :=
   Pairwise fun i j => ¬ G.Adj i j → (G.neighborSet i ∩ G.neighborSet j).ncard = 2

/--
Does there exist an undirected graph with 99 vertices, in which each two adjacent vertices have
exactly one common neighbor, and in which each two non-adjacent vertices have exactly two common
neighbors?
Equivalently, every edge should be part of a unique triangle and every non-adjacent pair should be
one of the two diagonals of a unique 4-cycle.
The first condition is equivalent to being locally linear.
-/
@[category research open, AMS 5]
theorem conway99Graph : (∃ G : SimpleGraph (Fin 99),
    G.LocallyLinear ∧ NonEdgesAreDiagonals G) ↔ answer(sorry) := by
  sorry

/--
The triangle is an example with 3 vertices satisfying the condition.
-/
@[category test, AMS 5]
theorem triangle_locallyLinear_and_nonEdgesAreDiagonals : (completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3)) := by
  constructor
  · simp [SimpleGraph.LocallyLinear]
    constructor
    · simp only [SimpleGraph.EdgeDisjointTriangles, Set.Pairwise]
      intro x hx y hy hxy
      have := @completeGraph_cliqueSet (Fin 3) _
      rw [Fintype.card_fin] at this
      rw [this] at hx hy
      rw [hx, hy] at hxy
      tauto
    · intro x y hxy
      use {x, y, 2 * x + 2 * y}
      fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> constructor <;> decide
  · tauto

/--
The box product of two triangles is an example with 9 vertices satisfying the condition.
(This graph is the complement of the one described in https://vimeo.com/109815595
and it is also isomorphic to it and to the Paley graph and the graph of the
3-3 duoprism)
-/
def Conway9 := (completeGraph (Fin 3)) □ (completeGraph (Fin 3))

@[category test, AMS 5]
theorem conway9_nonEdgesAreDiagonals : NonEdgesAreDiagonals Conway9 := by
  simp only [NonEdgesAreDiagonals, Set.Pairwise]
  have : ∀ i, Fintype ↑(Conway9.neighborSet i) := by
    intro i
    exact Fintype.ofFinite ↑(Conway9.neighborSet i)
  have : ∀ i j, ((Conway9.neighborFinset i) ∩ Conway9.neighborFinset j).card =
    (Conway9.neighborSet i ∩ Conway9.neighborSet j).ncard := by
    simp only [SimpleGraph.neighborFinset]
    intros
    rw [← Set.toFinset_inter, Set.ncard_eq_toFinset_card']
  simp only [← this]
  intro x y
  have ⟨x1, x2⟩ := x
  have ⟨y1, y2⟩ := y
  simp only [Conway9, SimpleGraph.completeGraph_eq_top,
    SimpleGraph.boxProd_adj, SimpleGraph.top_adj, SimpleGraph.boxProd_neighborFinset]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> decide

@[category API, AMS 5]
lemma completeGraph_boxProd_completeGraph_cliqueSet :
    ((completeGraph (Fin 3)) □ (completeGraph (Fin 3))).cliqueSet 3 =
    {({(p, q)| p} : Finset (Fin 3 × Fin 3)) | q } ∪
    {({(q, p)| p} : Finset (Fin 3 × Fin 3)) | q } := by
  sorry

@[category test, AMS 5]
theorem conway9_locallyLinear : Conway9.LocallyLinear := by
  dsimp [SimpleGraph.LocallyLinear]
  constructor
  · simp only [SimpleGraph.EdgeDisjointTriangles, Set.Pairwise]
    intro x hx y hy hxy
    simp only [Conway9, completeGraph_boxProd_completeGraph_cliqueSet] at hx hy
    rcases hx with hx | hx <;>
    rcases hy with hy | hy <;>
    have ⟨q, hx⟩ := hx <;>
    have ⟨p, hy⟩ := hy <;>
    rcases hx with hx | hx | hx <;>
    rcases hy with hy | hy | hy <;>
    fin_cases q <;>
    fin_cases p <;>
    simp only [Fin.mk_one, ne_eq, not_true_eq_false] at hxy <;>
    decide
  · intro x y
    have ⟨x1, x2⟩ := x
    have ⟨y1, y2⟩ := y
    intro h
    use {(x1, x2), (y1, y2), (x1 + x1 + y1 + y1, x2 + x2 + y2 + y2)}
    simp only [Finset.mem_insert, Prod.mk.injEq, true_or, or_true, and_true]
    simp only [Conway9, SimpleGraph.completeGraph_eq_top, SimpleGraph.boxProd_adj,
      SimpleGraph.top_adj, ne_eq] at h ⊢
    constructor
    · dsimp [SimpleGraph.IsClique, ]
      fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
      simp only [Fin.reduceFinMk,  not_true_eq_false, Fin.reduceEq, or_true, Fin.reduceAdd,
        Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_insert,
        Set.pairwise_singleton, Set.mem_singleton_iff, ne_eq, SimpleGraph.boxProd_adj,
        SimpleGraph.top_adj, forall_eq, Prod.mk.injEq, and_false, imp_self, Set.mem_insert_iff,forall_eq_or_imp, or_false, and_true, not_false_eq_true] at h ⊢
    · fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
      simp only [not_true_eq_false, or_self, or_false, and_true] at h <;>
      decide

end Conway99Graph
