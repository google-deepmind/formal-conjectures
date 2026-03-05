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
# Erdős Problem 807

*Reference:* [erdosproblems.com/807](https://www.erdosproblems.com/807)

Is it true that for a random graph $G$ on $n$ vertices with edge probability $1/2$,
$\tau(G) = n - \alpha(G)$ almost surely? Here $\tau(G)$ is the bipartition number (the
smallest number of pairwise edge-disjoint complete bipartite graphs whose union is $G$)
and $\alpha(G)$ is the independence number. Disproved by Alon [Al15].

[Al15] Alon, N., _Bipartite decomposition of random graphs_, J. Graph Theory, 2015.

[ABH17] Alon, N., Bohman, T. and Huang, H., _More on bipartite decomposition of random
graphs_, J. Graph Theory, 2017.
-/

open SimpleGraph Filter Classical

open scoped Topology

namespace Erdos807

/--
A biclique cover of a simple graph $G$ of size $k$ consists of $k$ complete bipartite
subgraphs (specified by pairs of disjoint vertex sets) that are pairwise
edge-disjoint and together cover all edges of $G$.
-/
def IsBicliqueCover {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (A B : Fin k → Set V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
  (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, G.Adj a b) ∧
  (∀ i j : Fin k, i ≠ j →
    ∀ v w : V, ¬((v ∈ A i ∧ w ∈ B i ∨ w ∈ A i ∧ v ∈ B i) ∧
                  (v ∈ A j ∧ w ∈ B j ∨ w ∈ A j ∧ v ∈ B j))) ∧
  (∀ v w : V, G.Adj v w →
    ∃ i : Fin k, (v ∈ A i ∧ w ∈ B i) ∨ (w ∈ A i ∧ v ∈ B i))

/--
The bipartition number $\tau(G)$ is the minimum number of pairwise edge-disjoint
complete bipartite subgraphs needed to cover all edges of $G$.
-/
noncomputable def bipartitionNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (A B : Fin k → Set V), IsBicliqueCover G k A B}

/--
The independence number $\alpha(G)$ of a finite graph is the maximum cardinality of
an independent set (a set of vertices with no edges between them).
-/
noncomputable def independenceNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, S.card = k ∧
    ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w}

/--
Erdős Problem 807 (disproved by Alon [Al15]):

Is it true that for a random graph $G$ on $n$ vertices with edge probability $1/2$,
$\tau(G) = n - \alpha(G)$ almost surely?

The bipartition number $\tau(G)$ is the smallest number of pairwise edge-disjoint
complete bipartite graphs whose union is $G$. The independence number $\alpha(G)$ is
the size of the largest independent set in $G$.

In the $G(n, 1/2)$ model every labeled graph on $n$ vertices is equally likely, so
"almost surely" means the proportion of graphs satisfying the property tends
to $1$ as $n \to \infty$.

Alon [Al15] showed this is false: almost surely $\tau(G) \leq n - \alpha(G) - 1$.
Alon, Bohman, and Huang [ABH17] proved there exists $c > 0$ such that
almost surely $\tau(G) \leq n - (1 + c)\alpha(G)$.
-/
@[category research solved, AMS 5 60]
theorem erdos_807 : answer(False) ↔
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) //
        bipartitionNumber G = n - independenceNumber G} : ℝ) /
      (Nat.card (SimpleGraph (Fin n)) : ℝ))
    atTop (nhds 1) := by
  sorry

end Erdos807
