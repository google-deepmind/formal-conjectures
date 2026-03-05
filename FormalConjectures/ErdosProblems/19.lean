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
# Erdős Problem 19

*Reference:* [erdosproblems.com/19](https://www.erdosproblems.com/19)

If $G$ is an edge-disjoint union of $n$ copies of $K_n$, then $\chi(G) = n$.

Conjectured by Erdős, Faber, and Lovász in 1972. Proved for all sufficiently
large $n$ by Kang, Kelly, Kühn, Methuku, and Osthus; the remaining small cases
are decidable (resolved up to a finite check).

[KKKMO21] Kang, D.Y., Kelly, T., Kühn, D., Methuku, A. and Osthus, D.,
_A proof of the Erdős–Faber–Lovász conjecture_, Annals of Mathematics (2023).
-/

open SimpleGraph

namespace Erdos19

/--
**Erdős–Faber–Lovász Conjecture** (Erdős Problem 19):

If $G$ is an edge-disjoint union of $n$ copies of $K_n$, then $\chi(G) = n$.

We formalize "$G$ is an edge-disjoint union of $n$ copies of $K_n$" as: there
exist $n$ cliques (vertex sets), each of size $n$, such that
- each clique is a complete subgraph of $G$ (an $n$-clique),
- any two distinct cliques share at most one vertex (equivalently, they are
  edge-disjoint, since two shared vertices would force a shared edge), and
- every edge of $G$ lies in some clique.

Proved for all sufficiently large $n$ by [KKKMO21].
-/
@[category research solved, AMS 5]
theorem erdos_19 (n : ℕ) (hn : 2 ≤ n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cliques : Fin n → Finset V)
    -- Each clique is a copy of $K_n$ in $G$
    (hclique : ∀ i : Fin n, G.IsNClique n (cliques i))
    -- Any two distinct cliques share at most one vertex (edge-disjointness)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ((cliques i) ∩ (cliques j)).card ≤ 1)
    -- Every edge of $G$ lies in some clique
    (hcover : ∀ u v : V, G.Adj u v → ∃ i : Fin n, u ∈ cliques i ∧ v ∈ cliques i) :
    G.chromaticNumber = n := by
  sorry

end Erdos19
