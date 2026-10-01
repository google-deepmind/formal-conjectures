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
# Erdős Problem 585

*References:*
- [erdosproblems.com/585](https://www.erdosproblems.com/585)
- [CJMM24] Chakraborti, D. and Janzer, O. and Methuku, A. and Montgomery, R., _Edge-disjoint
  cycles with the same vertex set_. [arXiv:2404.07190](https://arxiv.org/abs/2404.07190) (2024).
- [Er76b] Erdős, P., _Problems and results in graph theory and combinatorial analysis_.
  Proceedings of the Fifth British Combinatorial Conference (Univ. Aberdeen, Aberdeen, 1975)
  (1976), 169-192.
- [PRS95] Pyber, L. and Rödl, V. and Szemerédi, E., _Dense graphs without 3-regular subgraphs_.
  Journal of Combinatorial Theory, Series B 63 (1995), 41-54.
-/

@[expose] public section

open SimpleGraph Filter

namespace Erdos585

/--
`G` contains two edge-disjoint cycles with the same vertex set: cycles `p` and `q` of `G` that
visit the same vertices and traverse no common edge.
-/
def HasTwoEdgeDisjointCyclesSameVertexSet {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u u) (q : G.Walk v v), p.IsCycle ∧ q.IsCycle ∧
    {w | w ∈ p.support} = {w | w ∈ q.support} ∧ List.Disjoint p.edges q.edges

/--
`maxEdges n` is the maximum number of edges of a graph on `n` vertices that does not contain two
edge-disjoint cycles with the same vertex set. The set of edge counts contains `0` (the edgeless
graph) and is bounded by `n.choose 2`, so the supremum is attained.
-/
noncomputable def maxEdges (n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n), ¬ HasTwoEdgeDisjointCyclesSameVertexSet G ∧
    G.edgeSet.ncard = m}

/--
What is the maximum number of edges that a graph on $n$ vertices can have if it does not contain
two edge-disjoint cycles with the same vertex set?
-/
@[category research open, AMS 5]
theorem erdos_585 : ∀ n, maxEdges n = (answer(sorry) : ℕ → ℕ) n := by
  sorry

/--
What is the maximum number of edges that a graph on $n$ vertices can have if it does not contain
two edge-disjoint cycles with the same vertex set? Here the question asks for the order of growth.
-/
@[category research open, AMS 5]
theorem erdos_585.variants.isTheta :
    (fun n ↦ (maxEdges n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Pyber, Rödl, and Szemerédi [PRS95] constructed such a graph with $\gg n\log\log n$ edges.

Their graphs have no $4$-regular subgraph, and two edge-disjoint cycles with the same vertex set
form a $4$-regular graph [CJMM24].
-/
@[category research solved, AMS 5]
theorem erdos_585.variants.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G ∧
      c * (n : ℝ) * Real.log (Real.log n) ≤ G.edgeSet.ncard := by
  sorry

/--
Chakraborti, Janzer, Methuku, and Montgomery [CJMM24] have shown that such a graph can have at
most $n(\log n)^{O(1)}$ many edges. Indeed, they prove that there exists a constant $C>0$ such
that for any $k\geq 2$ there is a $c_k$ such that if a graph has $n$ vertices and at least
$c_kn(\log n)^{C}$ many edges then it contains $k$ pairwise edge-disjoint cycles with the same
vertex set.

This is the case $k = 2$ of [CJMM24, Theorem 2], with $t = C$ and $c = c_2$.
-/
@[category research solved, AMS 5]
theorem erdos_585.variants.upper_bound :
    ∃ t c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      c * (n : ℝ) * (Real.log n) ^ t ≤ G.edgeSet.ncard →
      HasTwoEdgeDisjointCyclesSameVertexSet G := by
  sorry

/--
The complete graph $K_5$ contains two edge-disjoint cycles with the same vertex set: it is the
union of the Hamiltonian cycles $0\,1\,2\,3\,4$ and $0\,2\,4\,1\,3$.
-/
@[category test, AMS 5]
theorem hasTwoEdgeDisjointCyclesSameVertexSet_top_five :
    HasTwoEdgeDisjointCyclesSameVertexSet (⊤ : SimpleGraph (Fin 5)) := by
  refine ⟨0, 0,
    .cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 0 1)
      (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 1 2)
        (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 2 3)
          (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 3 4)
            (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 4 0) .nil)))),
    .cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 0 2)
      (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 2 4)
        (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 4 1)
          (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 1 3)
            (.cons (by decide : (⊤ : SimpleGraph (Fin 5)).Adj 3 0) .nil)))),
    ?_, ?_, ?_, ?_⟩
  · rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨by decide, by simp, by decide⟩
  · rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨by decide, by simp, by decide⟩
  · ext w
    fin_cases w <;> simp
  · exact List.disjoint_toFinset_iff_disjoint.mp (by decide)

end Erdos585
