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
# Erdős Problem 614

*Reference:* [erdosproblems.com/614](https://www.erdosproblems.com/614)

Let $f(n,k)$ be minimal such that there is a graph with $n$ vertices and $f(n,k)$ edges
where every set of $k+2$ vertices induces a subgraph with maximum degree at least $k$.
Determine $f(n,k)$.

A problem of Erdős, Faudree, Rousseau, and Schelp.

[FRS97] Faudree, R., Rousseau, C., and Schelp, R., *Problems in graph theory from
Memphis*. The Mathematics of Paul Erdős, II (1997).
-/

open Classical SimpleGraph Finset

namespace Erdos614

/-- A graph $G$ on `Fin n` has the **$(n,k)$-induced degree property** if every subset of
exactly $k + 2$ vertices contains a vertex adjacent to at least $k$ other vertices
in the subset (i.e., the induced subgraph on that subset has maximum degree $\geq k$). -/
def HasInducedDegreeProp {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k + 2 →
    ∃ v ∈ S, k ≤ (S.filter (G.Adj v)).card

/-- `erdos614_f n k` is the minimum number of edges in a graph on $n$ vertices such that
every subset of $k + 2$ vertices induces a subgraph with maximum degree at least $k$.
This is the function $f(n, k)$ from Erdős Problem 614. -/
noncomputable def erdos614_f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.edgeFinset.card = m ∧ HasInducedDegreeProp G k}

/--
**Erdős Problem 614** [FRS97]:

Determine $f(n,k)$, the minimum number of edges in a graph on $n$ vertices such that every
subset of $k+2$ vertices induces a subgraph with maximum degree at least $k$.
-/
@[category research open, AMS 5]
theorem erdos_614 : ∀ n k : ℕ, n ≥ k + 2 →
    erdos614_f n k = answer(sorry) := by
  sorry

end Erdos614
