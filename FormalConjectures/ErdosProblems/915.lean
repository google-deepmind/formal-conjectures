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
# Erdős Problem 915

*References:*
- [erdosproblems.com/915](https://www.erdosproblems.com/915)
- [BoEr62] Bollobás, Béla and Erdős, Pál, *Extremal problems in graph theory*. Mat. Lapok (1962),
  143--152.
- [Er67b] Erdős, Paul, *Extremal problems in graph theory*. A Seminar on Graph Theory (1967),
  54-59.
- [Ba60] P. Bártfai, *Solution of a problem posed by P. Erdős*. Mat. Lapok (1960), 175-176.
- [Bo66] Bollobás, B., *On graphs with at most three independent paths connecting any two
  vertices*. Studia Sci. Math. Hungar. (1966), 137--140.
- [Le73] Leonard, John L., *On a conjecture of Bollobás and Erdős*. Period. Math. Hungar. (1973),
  281--284.
- [Ma73] Mader, W., *Ein Extremalproblem des Zusammenhangs von Graphen*. Math. Z. (1973),
  223--231.
- [SoTh74] Sørensen, Bo Aagaard and Thomassen, Carsten, *On $k$-rails in graphs*. J.
  Combinatorial Theory Ser. B (1974), 143--159.
-/

@[expose] public section

open SimpleGraph

namespace Erdos915

/--
Let $G$ be a graph with $1+n(m-1)$ vertices and $1+n\binom{m}{2}$ edges. Must $G$ contain two
points which are connected by $m$ disjoint paths?

A conjecture of Bollobás and Erdős [BoEr62]. This would be the best possible, as demonstrated by
$n$ copies of $K_m$ which share a single vertex (but are otherwise disjoint). It is unclear
whether disjoint here is to mean edge-disjoint or (internally) vertex-disjoint. The above
construction is valid for either interpretation.

This is the internally vertex-disjoint reading. It is trivial for $m = 2$, and was proved for
$m = 3$ by Bártfai [Ba60] and for $m = 4$ by Bollobás [Bo66]. Leonard [Le73] disproved this
conjecture for $m=5$, giving an explicit counterexample with $57$ vertices and $141$ edges, and
Mader [Ma73] disproved the conjecture in general for all $m \geq 6$. Sørensen and Thomassen
[SoTh74] proved that the conjectured bound of Bollobás and Erdős holds if the graph is
$3$-connected.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos915.lean#L362"]
theorem erdos_915 : answer(False) ↔
    ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) → G.edgeSet.ncard = 1 + n * m.choose 2 →
        ∃ u v : V, u ≠ v ∧ ∃ P : Finset (G.Walk u v), P.card = m ∧ (∀ p ∈ P, p.IsPath) ∧
          (P : Set (G.Walk u v)).Pairwise InternallyDisjoint := by
  sorry

/--
The edge-disjoint reading of [erdős_915](https://www.erdosproblems.com/915). Mader [Ma73] proved
that if a graph with $n$ vertices has more than
$$\frac{m}{2}(n-1)-\frac{1}{2}(e_0(G)+\cdots+e_{m-2}(G))$$
edges then $G$ contains two vertices connected by $m$ edge-disjoint paths (where $e_r(G)$ counts
the number of vertices of degree $\leq r$). In particular, this confirms (and is stronger than)
the conjecture.
-/
@[category research solved, AMS 5]
theorem erdos_915.variants.edge_disjoint : answer(True) ↔
    ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) → G.edgeSet.ncard = 1 + n * m.choose 2 →
        ∃ u v : V, u ≠ v ∧ ∃ P : Finset (G.Walk u v), P.card = m ∧ (∀ p ∈ P, p.IsPath) ∧
          (P : Set (G.Walk u v)).Pairwise fun p q => List.Disjoint p.edges q.edges := by
  sorry

end Erdos915
