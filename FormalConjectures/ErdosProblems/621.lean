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
# Erdős Problem 621

*Reference:* [erdosproblems.com/621](https://www.erdosproblems.com/621)

A problem of Erdős, Gallai, and Tuza on triangle-independent and triangle-transversal
edge sets in graphs. Proved by Norin and Sun.

[EGT96] Erdős, P., Gallai, T., and Tuza, Z., _Covering and independence in triangle
structures_, Discrete Mathematics 150 (1996), 89-101.

[NoSu16] Norin, S. and Sun, Y., _Triangle-independent sets vs. triangle-transversals_,
European Journal of Combinatorics 56 (2016), 95-104.
-/

open SimpleGraph

namespace Erdos621

/-- Create an unordered pair from two vertices, representing an edge. -/
abbrev mkEdge {V : Type*} (a b : V) : Sym2 V := Quot.mk _ (a, b)

/--
A set of edges $S$ is triangle-independent in $G$ if $S \subseteq E(G)$ and every
triangle in $G$ contains at most one edge from $S$.
-/
def IsTriangleIndependent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Sym2 (Fin n))) : Prop :=
  S ⊆ G.edgeFinset ∧
  ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c →
    ¬(mkEdge a b ∈ S ∧ mkEdge b c ∈ S) ∧
    ¬(mkEdge a b ∈ S ∧ mkEdge a c ∈ S) ∧
    ¬(mkEdge b c ∈ S ∧ mkEdge a c ∈ S)

/--
A set of edges $T$ is a triangle transversal in $G$ if $T \subseteq E(G)$ and every
triangle in $G$ contains at least one edge from $T$.
-/
def IsTriangleTransversal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Sym2 (Fin n))) : Prop :=
  T ⊆ G.edgeFinset ∧
  ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c →
    mkEdge a b ∈ T ∨ mkEdge b c ∈ T ∨ mkEdge a c ∈ T

/--
**Erdős Problem 621** (Erdős-Gallai-Tuza conjecture) [EGT96]:

Let $G$ be a graph on $n$ vertices. Define $\alpha_1(G)$ as the maximum number of edges
forming a set that contains at most one edge from every triangle, and $\tau_1(G)$ as
the minimum number of edges forming a set that contains at least one edge from
every triangle.

Conjecture: $\alpha_1(G) + \tau_1(G) \leq n^2/4$.

This was proved by Norin and Sun [NoSu16].
-/
@[category research solved, AMS 5]
theorem erdos_621 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Sym2 (Fin n)))
    (hS : IsTriangleIndependent G S)
    (hS_max : ∀ S' : Finset (Sym2 (Fin n)), IsTriangleIndependent G S' → S'.card ≤ S.card)
    (T : Finset (Sym2 (Fin n)))
    (hT : IsTriangleTransversal G T)
    (hT_min : ∀ T' : Finset (Sym2 (Fin n)), IsTriangleTransversal G T' → T.card ≤ T'.card) :
    4 * (S.card + T.card) ≤ n ^ 2 := by
  sorry

end Erdos621
