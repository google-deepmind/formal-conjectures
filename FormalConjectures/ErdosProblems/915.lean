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
# Erdős Problem 915

*References:*
- [erdosproblems.com/915](https://www.erdosproblems.com/915)
- [BoEr62] Bollobás, Béla and Erdős, Pál, *Extremal problems in graph theory*.
  Mat. Lapok (1962), 143--152.
- [Le73] Leonard, John L., *On a conjecture of Bollobás and Erdős*.
  Period. Math. Hungar. (1973), 281--284.
- [Ma73] Mader, W., *Ein Extremalproblem des Zusammenhangs von Graphen*.
  Math. Z. (1973), 223--231.
- [SoTh74] Sørensen, Bo Aagaard and Thomassen, Carsten, *On $k$-rails in graphs*.
  J. Combinatorial Theory Ser. B (1974), 143--159.
-/

open SimpleGraph

namespace Erdos915

/--
`HasInternallyDisjointPaths G u v m` means there are $m$ internally vertex-disjoint $u$-$v$ paths
in $G$.
-/
def HasInternallyDisjointPaths {V : Type*} (G : SimpleGraph V) (u v : V) (m : ℕ) : Prop :=
  ∃ P : Set (G.Walk u v),
    P.ncard = m ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/--
`HasEdgeDisjointPaths G u v m` means there are $m$ edge-disjoint $u$-$v$ paths in $G$.
-/
def HasEdgeDisjointPaths {V : Type*} (G : SimpleGraph V) (u v : V) (m : ℕ) : Prop :=
  ∃ P : Set (G.Walk u v),
    P.ncard = m ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise fun p q ↦ Disjoint p.edgeSet q.edgeSet

/--
Let $G$ be a graph with $1+n(m-1)$ vertices and $1+n\binom{m}{2}$ edges. Must $G$ contain two
points which are connected by $m$ disjoint paths?

A conjecture of Bollobás and Erdős [BoEr62]. This would be best possible, as demonstrated by $n$
copies of $K_m$ which share a single vertex (but are otherwise disjoint).

It is unclear whether disjoint here is to mean edge-disjoint or (internally) vertex-disjoint. The
above construction is valid for either interpretation. This statement uses internally
vertex-disjoint paths, matching the function $k_m(n)$ on the problem page: the conjecture is that
for all $m\geq 2$,
$$
k_m(1+(m-1)n)=1+\binom{m}{2}n.
$$

The vertex-disjoint conjecture is false. Leonard [Le73] gave a counterexample for $m=5$ with $57$
vertices and $141$ edges. Sørensen and Thomassen [SoTh74] determined $k_5(n)$ exactly for
$n\geq 13$. Mader [Ma73] disproved the conjecture for all $m\geq 6$.
-/
@[category research solved, AMS 5]
theorem erdos_915 : answer(False) ↔
    ∀ (n m : ℕ), 2 ≤ m → ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) →
      G.edgeSet.ncard = 1 + n * m.choose 2 →
        ∃ u v : V, u ≠ v ∧ HasInternallyDisjointPaths G u v m := by
  sorry

/--
The same question, reading “disjoint paths” as edge-disjoint (the function $\ell_m(n)$ on the
problem page).

Mader [Ma73] confirmed this interpretation, and in fact proved
$$
\ell_m(n)=\left\lfloor \frac{m}{2}(n-1)+1\right\rfloor
$$
for all $m\geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_915.variants.edgeDisjoint : answer(True) ↔
    ∀ (n m : ℕ), 2 ≤ m → ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) →
      G.edgeSet.ncard = 1 + n * m.choose 2 →
        ∃ u v : V, u ≠ v ∧ HasEdgeDisjointPaths G u v m := by
  sorry

end Erdos915
