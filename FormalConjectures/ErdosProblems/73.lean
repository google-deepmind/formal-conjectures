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

See also: Erdős Problem 922 (related independent-set condition yielding bounded chromatic
number).

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large chromatic graphs_,
Annals of Discrete Mathematics 12 (1982), 117–123.

[Re99] Reed, B., _Mangoes and blueberries_. Combinatorica 19 (1999), 267–296.
-/

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
        -- The condition `2 * I.card ≥ S.card - k` encodes |I| ≥ (|S| - k) / 2.
        (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), I ⊆ S ∧ G.IsIndepSet ↑I ∧
          2 * I.card ≥ S.card - k) →
        ∃ T : Finset (Fin n), T.card ≤ C ∧
          ∃ f : Fin n → Bool, ∀ ⦃u v⦄, u ∉ T → v ∉ T → G.Adj u v → f u ≠ f v := by
  sorry

/--
The $k = 0$ case of Erdős Problem 73: if every vertex subset $S$ of $G$ contains
an independent set of size $\geq |S| / 2$, then $G$ is bipartite (no vertex removal needed).

This is trivial: a non-bipartite graph contains an odd cycle, which violates the
independent-set hypothesis. Noted by Reed [Re99].
-/
@[category research solved, AMS 5]
theorem erdos_73.variants.k_eq_zero :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), I ⊆ S ∧ G.IsIndepSet ↑I ∧
        2 * I.card ≥ S.card) →
      ∃ f : Fin n → Bool, ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v := by
  sorry

end Erdos73
