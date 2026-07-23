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
# Erdős Problem 794

*References:*
- [erdosproblems.com/794](https://www.erdosproblems.com/794)
- [Er69] Erdős, Paul, *Some applications of graph theory to number theory*. The Many Facets of
  Graph Theory (Proc. Conf., Western Mich. Univ., Kalamazoo, Mich., 1968) (1969), 77-82.
- [FrFu84] Frankl, P. and Füredi, Z., *An exact result for $3$-graphs*. Discrete Math. (1984),
  323-328.
-/

open Filter

namespace Erdos794

/-- A finite family `H` of sets of vertices is a *`3`-uniform hypergraph* if every edge of `H`
has exactly `3` vertices. -/
def IsThreeUniform {V : Type*} (H : Finset (Finset V)) : Prop := ∀ e ∈ H, e.card = 3

/-- `ContainsSubgraph H m k` holds when some set of `m` vertices spans at least `k` edges of
`H`, that is, when `H` contains a subgraph on `m` vertices with `k` edges. -/
def ContainsSubgraph {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (m k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = m ∧ k ≤ (Finset.filter (fun e : Finset V => e ⊆ S) H).card

/-- The `3`-uniform hypergraph on `Fin 9` given by Harris: the `27` triples containing exactly
one vertex from each of the three parts `{0, 1, 2}`, `{3, 4, 5}`, `{6, 7, 8}`, together with the
triple `{0, 1, 2}`. A triple is a transversal of the three parts exactly when the three values
of `v ↦ v / 3` it produces are distinct. -/
def harrisHypergraph : Finset (Finset (Fin 9)) :=
  insert {0, 1, 2}
    (Finset.filter
      (fun e : Finset (Fin 9) =>
        (Finset.image (fun v : Fin 9 => (v : ℕ) / 3) e).card = 3)
      (Finset.powersetCard 3 Finset.univ))

/--
Is it true that every $3$-uniform hypergraph on $3n$ vertices with at least $n^3+1$ edges must
contain either a subgraph on $4$ vertices with $3$ edges or a subgraph on $5$ vertices with $7$
edges?

Harris has provided the following simple counterexample to the problem as stated: the
$3$-uniform graph on $\{1,\ldots,9\}$ with $28$ edges, formed by taking $27$ edges by choosing
one element each from $\{1,2,3\},\{4,5,6\},\{7,8,9\}$, and then adding the edge $\{1,2,3\}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos794.lean"]
theorem erdos_794 : answer(False) ↔
    ∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))), IsThreeUniform H →
      n ^ 3 + 1 ≤ H.card → ContainsSubgraph H 4 3 ∨ ContainsSubgraph H 5 7 := by
  sorry

/--
Balogh has observed that this problem is probably misstated by Erdős - indeed, every graph with
$5$ vertices spanning $7$ edges contains a graph on $4$ vertices spanning $3$ edges, so the
second condition can be dropped.
-/
@[category research solved, AMS 5]
theorem erdos_794.variants.balogh {V : Type*} [DecidableEq V] (H : Finset (Finset V))
    (hH : IsThreeUniform H) (h : ContainsSubgraph H 5 7) : ContainsSubgraph H 4 3 := by
  sorry

/--
Harris has provided the following simple counterexample to the problem as stated: the
$3$-uniform graph on $\{1,\ldots,9\}$ with $28$ edges, formed by taking $27$ edges by choosing
one element each from $\{1,2,3\},\{4,5,6\},\{7,8,9\}$, and then adding the edge $\{1,2,3\}$.
-/
@[category research solved, AMS 5]
theorem erdos_794.variants.harris :
    IsThreeUniform harrisHypergraph ∧ harrisHypergraph.card = 28 ∧
      ¬ ContainsSubgraph harrisHypergraph 4 3 ∧ ¬ ContainsSubgraph harrisHypergraph 5 7 := by
  sorry

/--
This problem is then now asking how many edges a $3$-uniform hypergraph can have before it
contains $K_4$ minus an edge, and whether the critical edge density is $2/9$. In fact there is a
construction of Frankl and Füredi [FrFu84] showing it must be at least $2/7$, which is the
conjectured truth (although Turán conjectured before [Er69] that the edge density was $1/4$, and
so likely there is simply a typo in this problem's statement).
-/
@[category research solved, AMS 5]
theorem erdos_794.variants.frankl_furedi (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset (Fin n)), IsThreeUniform H ∧
      ¬ ContainsSubgraph H 4 3 ∧ (2 / 7 - ε) * (n.choose 3 : ℝ) ≤ (H.card : ℝ) := by
  sorry

end Erdos794
