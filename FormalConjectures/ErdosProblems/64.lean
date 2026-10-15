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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 64

*References:*
- [erdosproblems.com/64](https://www.erdosproblems.com/64)
- [J. J. Gebendorfer, Power-of-Two Cycles in Cubic Bipartite Vertex-Transitive Graphs of Girth Six: A universal proof by alternating first returns and hexagonal fans, 8 September 2026; written proof and scoped intake](https://github.com/google-deepmind/formal-conjectures/issues/7281)
- [P. Potočnik and J. Vidali, structural classification used in the written proof](https://arxiv.org/pdf/2005.01635)
- [B. Alspach, honeycomb toroidal cycle spectrum used in the written proof](https://arxiv.org/pdf/2007.05133)
-/

@[expose] public section

namespace Erdos64

/--
Does every finite graph with minimum degree at least $3$
contain a cycle of length $2^k$ for some $k \geq 2$?
-/
@[category research open, question, AMS 5]
theorem erdos_64 :
    ∀ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
        G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
            k ≥ 2 ∧ c.IsCycle ∧ c.length = 2^k := by
  sorry

/-- A spanning two-factor of hexagons, with no additional simple six-cycles
in the ambient graph. Components are counted by their actual vertex supports. -/
noncomputable def HasExactHexagonFactor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ F : SimpleGraph V, F ≤ G ∧ (∀ v, F.degree v = 2) ∧
    (∀ v, Nat.card (F.connectedComponentMk v).supp = 6) ∧
    ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length = 6 →
      ∀ e ∈ c.edges, e ∈ F.edgeFinset

/-- Every nonempty finite simple cubic bipartite vertex-transitive graph of
girth six contains a simple cycle of length $2^k$ for some $k\ge3$.
This is the restricted all-order statement in the cited written proof, not a
resolution of the unrestricted minimum-degree-three problem. The classification
and honeycomb spectrum inputs are credited in that source. -/
@[category research solved, AMS 5]
theorem erdos_64.variants.cubic_bipartite_vertex_transitive_girth_six
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : ∀ v, G.degree v = 3)
    (hb : G.IsBipartite) (hg : G.girth = 6)
    (ht : ∀ u v : V, ∃ e : G ≃g G, e u = v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 3 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  sorry

/-- A nonempty finite simple cubic bipartite graph of girth six whose simple
hexagons are exactly a spanning two-factor has a simple dyadic cycle of length
at most $5|V|/6$. Transitivity and an order cutoff are not assumed. -/
@[category research solved, AMS 5]
theorem erdos_64.variants.exact_hexagon_factor
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : ∀ v, G.degree v = 3)
    (hb : G.IsBipartite) (hg : G.girth = 6) (hf : HasExactHexagonFactor G) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 3 ≤ k ∧ c.IsCycle ∧
      c.length = 2^k ∧ 6 * c.length ≤ 5 * Fintype.card V := by
  sorry

-- TODO(firsching): add more context

end Erdos64
