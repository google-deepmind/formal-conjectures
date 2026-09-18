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
# Erdős Problem 816

*References:*
- [erdosproblems.com/816](https://www.erdosproblems.com/816)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [ChMa25] K. Chen and J. Ma, *A problem of Erdős and Hajnal on paths with equal-degree
  endpoints*. arXiv:2503.19569 (2025).
-/

@[expose] public section

open SimpleGraph

namespace Erdos816

open scoped Classical in
/--
`G` contains two vertices of the same degree which are joined by a path of length `3`.
-/
def HasEqualDegreePathThree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3

open scoped Classical in
/--
Let $G$ be a graph with $2n+1$ vertices and $n^2+n+1$ edges. Must $G$ contain two vertices of the
same degree which are joined by a path of length $3$?

A problem of Erdős and Hajnal. The example of $K_{n,n+1}$ shows that this fails if we only have
$n^2+n$ edges.

This is true, and was proved by Chen and Ma [ChMa25], who prove the stronger statement that,
provided $n\geq 600$, all graphs with $2n+1$ vertices and at least $n^2+n$ edges contain two
vertices of the same degree joined by a path of length $3$, except $K_{n,n+1}$.

For $n = 1$ the graph is a triangle, which contains no path of length $3$, so we assume $n \geq 2$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos816.lean#L939"]
theorem erdos_816 : answer(True) ↔ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin (2 * n + 1)),
    G.edgeFinset.card = n ^ 2 + n + 1 → HasEqualDegreePathThree G := by
  sorry

open scoped Classical in
/--
Chen and Ma [ChMa25] proved that, provided $n\geq 600$, all graphs with $2n+1$ vertices and at
least $n^2+n$ edges contain two vertices of the same degree joined by a path of length $3$, except
$K_{n,n+1}$.
-/
@[category research solved, AMS 5]
theorem erdos_816.variants.chen_ma : ∀ n : ℕ, 600 ≤ n →
    ∀ G : SimpleGraph (Fin (2 * n + 1)), n ^ 2 + n ≤ G.edgeFinset.card →
      ¬ Nonempty (G ≃g completeBipartiteGraph (Fin n) (Fin (n + 1))) →
        HasEqualDegreePathThree G := by
  sorry

open scoped Classical in
/-- The example of $K_{n,n+1}$ shows that this fails if we only have $n^2+n$ edges. -/
@[category research solved, AMS 5]
theorem erdos_816.variants.complete_bipartite : ∀ n : ℕ,
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).edgeFinset.card = n ^ 2 + n ∧
      ¬ HasEqualDegreePathThree (completeBipartiteGraph (Fin n) (Fin (n + 1))) := by
  sorry

end Erdos816
