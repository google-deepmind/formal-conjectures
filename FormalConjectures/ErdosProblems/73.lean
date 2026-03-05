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
# Erdős Problem 73

*Reference:* [erdosproblems.com/73](https://www.erdosproblems.com/73)

If every induced subgraph of $G$ on $n$ vertices has an independent set of size
$\geq (n - k)/2$, then removing $O_k(1)$ vertices makes $G$ bipartite.
Proved by Reed [Re99].

[Re99] Reed, B., _Mangoes and blueberries_. Combinatorica 19 (1999), 267–296.
-/

/--
An independent set of a simple graph within a vertex subset $S$:
a subset $I \subseteq S$ such that no two vertices in $I$ are adjacent in $G$.
-/
def SimpleGraph.IndepSetIn {V : Type*} (G : SimpleGraph V)
    (I S : Finset V) : Prop :=
  I ⊆ S ∧ ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → u ≠ v → ¬G.Adj u v

namespace Erdos73

/--
Let $k \geq 0$. If $G$ is a finite graph such that every induced subgraph $H$ on $n$
vertices contains an independent set of size $\geq (n - k) / 2$, then there exists
a set $S$ of $O_k(1)$ vertices whose removal makes $G$ bipartite.

Equivalently: for every $k$, there exists a constant $C$ (depending only on $k$)
such that for any finite graph $G$ on $n$ vertices, if every vertex subset $S$
contains an independent set of size at least $(|S| - k) / 2$, then $G$ can be
made bipartite by removing at most $C$ vertices.

Proved by Reed [Re99].
-/
@[category research solved, AMS 5]
theorem erdos_73 : answer(True) ↔
    ∀ k : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), G.IndepSetIn I S ∧
          2 * I.card ≥ S.card - k) →
        ∃ T : Finset (Fin n), T.card ≤ C ∧
          ∃ f : Fin n → Bool, ∀ ⦃u v⦄, u ∉ T → v ∉ T → G.Adj u v → f u ≠ f v := by
  sorry

end Erdos73
