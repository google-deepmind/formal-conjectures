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
# Erdős Problem 151

Erdős and Gallai conjectured that the clique transversal number of any graph on $n$ vertices
is at most $n - H(n)$, where $H(n)$ is the minimum independence number over all triangle-free
graphs on $n$ vertices.

*Reference:* [erdosproblems.com/151](https://www.erdosproblems.com/151)

[Er88] Erdős, P., _Problems and results on chromatic numbers in finite and infinite graphs_,
1988, p.82.

[EGT92] Erdős, P., Gallai, T. and Tuza, Zs., _Covering the cliques of a graph with vertices_,
1992, p.280.
-/

open SimpleGraph

namespace Erdos151

/-- $S$ is a maximal clique of $G$ (represented as a `Finset`): it is a clique and
no vertex outside $S$ can be added while preserving the clique property. -/
def IsMaximalCliqueFS {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- $T$ is a clique transversal of $G$ if $T$ has non-empty intersection with every
maximal clique of $G$ that has at least $2$ vertices. -/
def IsCliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number $\tau(G)$: the minimum cardinality of a clique
transversal of $G$. -/
noncomputable def cliqueTransversalNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k }

/-- $S$ is an independent set in $G$: no two distinct vertices of $S$ are adjacent. -/
def IsIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- The independence number $\alpha(G)$: the maximum cardinality of an independent set. -/
noncomputable def independenceNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = k }

/-- $H(n)$ is maximal such that every triangle-free graph on $n$ vertices contains
an independent set of size $H(n)$; equivalently, $H(n)$ is the minimum
independence number over all triangle-free graphs on $n$ vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ independenceNumber G = k }

/--
Erdős Problem 151 [Er88, p.82] [EGT92, p.280] (problem of Erdős and Gallai):
If $G$ is a graph on $n$ vertices then $\tau(G) \leq n - H(n)$,
where $\tau(G)$ is the clique transversal number of $G$ and $H(n)$ is the maximum $k$
such that every triangle-free graph on $n$ vertices contains an independent set
of size $k$.
-/
@[category research open, AMS 5]
theorem erdos_151 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      cliqueTransversalNumber G ≤ n - H n := by
  sorry

end Erdos151
