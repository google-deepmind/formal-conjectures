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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 619

*References:*
- [erdosproblems.com/619](https://www.erdosproblems.com/619)
- [EGR98] Erdős, Paul and Gyárfás, András and Ruszinkó, Miklós, *How to decrease the
  diameter of triangle-free graphs*. Combinatorica **18** (1998), 493-501.
- [Er99] Erdős, Paul, *A selection of problems and results in combinatorics*.
  Combin. Probab. Comput. **8** (1999), 1-6.
-/

open SimpleGraph

namespace Erdos619

/--
For a graph $G$, `minNewEdges r G` is the smallest number of edges that need to be added
to $G$ so that it has diameter at most $r$, while preserving the property of being
triangle-free. Erdős, Gyárfás and Ruszinkó denote this quantity by $h_r(G)$ in [EGR98].

Adding edges is formalised as passing to a supergraph `H ≥ G` on the same vertex set, the
number of added edges being the (finite) cardinality of the edge set of `H \ G`. We use
the extended diameter `SimpleGraph.ediam` (valued in `ℕ∞`) so that disconnected
supergraphs, which have infinite diameter, do not qualify. If no triangle-free supergraph
of `G` of diameter at most `r` exists, then `minNewEdges r G = 0` by the `Nat.sInf`
convention on the empty set; `erdos_619.variants.add_edges_diam_three` shows this
degenerate case does not occur for connected triangle-free `G` when `3 ≤ r`.
-/
noncomputable def minNewEdges {V : Type*} (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ H : SimpleGraph V,
    G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ r ∧ (H \ G).edgeSet.ncard = k}

/--
**Erdős Problem 619** [EGR98, Er99]: For a triangle-free graph $G$ let $h_r(G)$ be the
smallest number of edges that need to be added to $G$ so that it has diameter $r$ (while
preserving the property of being triangle-free). Is it true that there exists a constant
$c>0$ such that if $G$ is a connected graph on $n$ vertices then $h_4(G)<(1-c)n$?
-/
@[category research open, AMS 5]
theorem erdos_619 : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.Connected → G.CliqueFree 3 →
      (minNewEdges 4 G : ℝ) < (1 - c) * Fintype.card V := by
  sorry

/-
## Partial results
-/

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: every connected triangle-free graph on a finite
vertex set can be extended, by adding edges, to a triangle-free graph of diameter at
most $3$. This shows that the infimum defining `minNewEdges r G` ranges over a nonempty
set for every `3 ≤ r`.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.add_edges_diam_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ 3 := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: $h_3(G) \leq n$ for every connected triangle-free
graph $G$ on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_three_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    minNewEdges 3 G ≤ Fintype.card V := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: $h_5(G) \leq \frac{n-1}{2}$ for every connected
triangle-free graph $G$ on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_five_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    (minNewEdges 5 G : ℝ) ≤ (Fintype.card V - 1) / 2 := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: there is a constant $c > 0$ such that for every
$n$ there exist connected triangle-free graphs $G$ on $n$ vertices with
$h_3(G) \geq n - c$.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_three_lower :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n ∧ G.Connected ∧ G.CliqueFree 3 ∧
        (n : ℝ) - c ≤ minNewEdges 3 G := by
  sorry

/-
## Sanity checks
-/

/-- A triangle-free graph that already has diameter at most `r` needs no new edges. -/
@[category test, AMS 5]
theorem erdos_619.test.minNewEdges_eq_zero {V : Type*} {r : ℕ} {G : SimpleGraph V}
    (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    minNewEdges r G = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inl ⟨G, le_rfl, hG, hdiam, by simp⟩

/-- The graph with a single vertex is triangle-free and has diameter `0`, so it needs no
new edges to reach diameter at most `4`. -/
@[category test, AMS 5]
theorem erdos_619.test.minNewEdges_singleton :
    minNewEdges 4 (⊥ : SimpleGraph (Fin 1)) = 0 :=
  erdos_619.test.minNewEdges_eq_zero (cliqueFree_bot (by norm_num))
    (by simp [ediam_eq_zero_of_subsingleton])

end Erdos619
