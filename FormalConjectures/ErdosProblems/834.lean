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
# Erdős Problem 834

*References:*
- [erdosproblems.com/834](https://www.erdosproblems.com/834)
- [Er74d] Erdős, Paul, *Unsolved Problems*. (1974), 278-297.
- [Li25] R. Li, *On an Erdős-Lovász problem: $3$-critical $3$-graphs of minimum degree $7$*.
  arXiv:2512.24850 (2025).
-/

@[expose] public section

open ThreeUniformHypergraph

namespace Erdos834

variable {V : Type}

/--
`H` is *$3$-critical* in the chromatic sense: it has chromatic number `3`, but its chromatic
number becomes `2` after deleting any edge or any vertex.
-/
def IsChromaticThreeCritical (H : ThreeUniformHypergraph V) : Prop :=
  (∃ f : V → Fin 3, H.IsProperColoring f) ∧ ¬ H.IsTwoColorable ∧
    (∀ e ∈ H.edges, (H.deleteEdge e).IsTwoColorable) ∧ ∀ v, (H.deleteVertex v).IsTwoColorable

/--
`H` is *$3$-critical* in the transversal sense: there is a set of `3` vertices which meets every
edge, but no such set of size `2`, and yet for any edge `e` there is a pair of vertices which
meets every edge except `e`.
-/
def IsTransversalThreeCritical (H : ThreeUniformHypergraph V) : Prop :=
  (∃ T : Finset V, T.card = 3 ∧ H.IsTransversal T) ∧
    (∀ T : Finset V, T.card ≤ 2 → ¬ H.IsTransversal T) ∧
    ∀ e ∈ H.edges, ∃ T : Finset V, T.card ≤ 2 ∧ (H.deleteEdge e).IsTransversal T

/--
Does there exist a $3$-critical $3$-uniform hypergraph in which every vertex has degree
$\geq 7$?

A problem of Erdős and Lovász. They do not specify what is meant by $3$-critical. One definition
in the literature is: a hypergraph is $3$-critical if there is a set of $3$ vertices which
intersects every edge, but no such set of size $2$, and yet for any edge $e$ there is a pair of
vertices which intersects every edge except $e$. Raphael Steiner observes that a $3$-critical
hypergraph in this sense has bounded size, so this problem would be a finite computation, and
perhaps is not what they meant.

An alternative definition is that a hypergraph is $3$-critical if it has chromatic number $3$,
but its chromatic number becomes $2$ after deleting any edge or vertex.

In either case, this has been resolved by Li [Li25]. In the chromatic notion of criticality
(formalised here), Li provides an explicit $3$-critical $3$-uniform hypergraph on $9$ vertices
with minimum degree $7$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos834.lean#L814"]
theorem erdos_834 : answer(True) ↔ ∃ (V : Type) (_ : Fintype V) (H : ThreeUniformHypergraph V),
    IsChromaticThreeCritical H ∧ ∀ v, 7 ≤ H.degree v := by
  sorry

/--
In the transversal notion of criticality, Li [Li25] proves that a $3$-critical $3$-uniform
hypergraph must have a vertex of degree $\leq 6$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos834.lean#L814"]
theorem erdos_834.variants.transversal : answer(False) ↔
    ∃ (V : Type) (_ : Fintype V) (H : ThreeUniformHypergraph V),
      IsTransversalThreeCritical H ∧ ∀ v, 7 ≤ H.degree v := by
  sorry

/--
Li [Li25] provides an explicit chromatically $3$-critical $3$-uniform hypergraph on $9$ vertices
with minimum degree $7$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos834.lean#L814"]
theorem erdos_834.variants.nine_vertices : ∃ H : ThreeUniformHypergraph (Fin 9),
    IsChromaticThreeCritical H ∧ ∀ v, 7 ≤ H.degree v := by
  sorry

end Erdos834
