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
# The 1-2-3 conjecture (Karoński–Łuczak–Thomason 2004; proved by Keusch 2024)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/1-2-3_conjecture)
* [KLT04] Karoński, M., Łuczak, T. and Thomason, A. (2004). "Edge weights and vertex colours."
  *J. Combin. Theory Ser. B* 91, pp. 151--157.
* [KKP10] Kalkowski, M., Karoński, M. and Pfender, F. (2010). "Vertex-coloring edge-weightings:
  towards the 1-2-3-conjecture." *J. Combin. Theory Ser. B* 100, pp. 347--349.
* [Ke24] Keusch, R. (2024). "A solution to the 1-2-3 conjecture."
  *J. Combin. Theory Ser. B* 166, pp. 183--202.
  [arXiv:2303.02611](https://arxiv.org/abs/2303.02611)
-/

open SimpleGraph Finset

namespace OneTwoThreeConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **weighted degree** of `v` under the edge weighting `w`: the sum of the weights of the
edges incident to `v`. -/
def weightedDegree (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ G.incidenceFinset v, w e

/-- An edge weighting `w` of `G` is **vertex-colouring** if adjacent vertices receive different
weighted degrees. -/
def IsVertexColouringWeighting (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → weightedDegree G w u ≠ weightedDegree G w v

/-- `G` has **no isolated edge**: no edge has both endpoints of degree `1` (equivalently, no
connected component is a single edge). -/
def NoIsolatedEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v

/--
**The 1-2-3 conjecture (Karoński–Łuczak–Thomason 2004), proved by Keusch (2024).**

Every finite simple graph with no isolated edge admits an edge weighting with weights in
$\{1, 2, 3\}$ such that adjacent vertices have different weighted degrees.
-/
@[category research solved, AMS 5]
theorem one_two_three_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      NoIsolatedEdge G →
      ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 3) ∧
        IsVertexColouringWeighting G w := by
  sorry

/--
**Kalkowski–Karoński–Pfender (2010): weights in $\{1, \dots, 5\}$ suffice.**

*Reference:* [KKP10].
-/
@[category research solved, AMS 5]
theorem one_two_three_conjecture.variants.one_to_five
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 5) ∧
      IsVertexColouringWeighting G w := by
  sorry

/--
**The original bound (Karoński–Łuczak–Thomason 2004): weights in $\{1, \dots, 30\}$ suffice.**

*Reference:* [KLT04].
-/
@[category research solved, AMS 5]
theorem one_two_three_conjecture.variants.one_to_thirty
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 30) ∧
      IsVertexColouringWeighting G w := by
  sorry

/--
**The hypothesis "no isolated edge" is necessary.**

A single edge `K₂` has no vertex-colouring edge weighting at all: both endpoints receive the
weight of the unique edge as their weighted degree.
-/
@[category research solved, AMS 5]
theorem one_two_three_conjecture.variants.isolated_edge_necessary :
    ¬ ∃ w : Sym2 (Fin 2) → ℕ, IsVertexColouringWeighting (completeGraph (Fin 2)) w := by
  rintro ⟨w, hw⟩
  refine hw 0 1 (by decide) ?_
  have h : ∀ v : Fin 2, (completeGraph (Fin 2)).incidenceFinset v = {s(0, 1)} := by
    intro v
    ext e
    rw [mem_incidenceFinset, Finset.mem_singleton]
    refine ⟨fun ⟨he, hv⟩ => ?_, fun he => ?_⟩
    · induction e with
      | h a b =>
        rw [mem_edgeSet, completeGraph_eq_top, top_adj] at he
        fin_cases a <;> fin_cases b <;> first | exact absurd rfl he | rfl | exact Sym2.eq_swap
    · subst he
      refine ⟨by rw [mem_edgeSet, completeGraph_eq_top, top_adj]; decide, ?_⟩
      fin_cases v <;> simp
  simp only [weightedDegree, h, Finset.sum_singleton]

/--
**Weights $\{1, 2\}$ do not suffice: the triangle.**

In `K₃` the three vertex sums are `a + b`, `a + c`, `b + c` for the three edge weights
`a, b, c`, and they are pairwise distinct only if `a, b, c` are, which is impossible with
two available weights. Hence the constant `3` in the conjecture cannot be lowered to `2`.
-/
@[category research solved, AMS 5]
theorem one_two_three_conjecture.variants.two_weights_insufficient :
    ¬ ∃ w : Sym2 (Fin 3) → ℕ, (∀ e ∈ (completeGraph (Fin 3)).edgeFinset, 1 ≤ w e ∧ w e ≤ 2) ∧
      IsVertexColouringWeighting (completeGraph (Fin 3)) w := by
  rintro ⟨w, hw, hcol⟩
  have h0 : (completeGraph (Fin 3)).incidenceFinset 0 = {s(0, 1), s(0, 2)} := by decide
  have h1 : (completeGraph (Fin 3)).incidenceFinset 1 = {s(0, 1), s(1, 2)} := by decide
  have h2 : (completeGraph (Fin 3)).incidenceFinset 2 = {s(0, 2), s(1, 2)} := by decide
  have e01 : s((0 : Fin 3), 1) ∈ (completeGraph (Fin 3)).edgeFinset := by decide
  have e02 : s((0 : Fin 3), 2) ∈ (completeGraph (Fin 3)).edgeFinset := by decide
  have e12 : s((1 : Fin 3), 2) ∈ (completeGraph (Fin 3)).edgeFinset := by decide
  have ha := hw _ e01
  have hb := hw _ e02
  have hc := hw _ e12
  have d01 := hcol 0 1 (by decide)
  have d02 := hcol 0 2 (by decide)
  have d12 := hcol 1 2 (by decide)
  simp only [weightedDegree, h0, h1, h2, Finset.sum_pair (by decide : s((0 : Fin 3), 1) ≠ s(0, 2)),
    Finset.sum_pair (by decide : s((0 : Fin 3), 1) ≠ s(1, 2)),
    Finset.sum_pair (by decide : s((0 : Fin 3), 2) ≠ s(1, 2))] at d01 d02 d12
  omega

end OneTwoThreeConjecture
