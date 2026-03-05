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
# Erdős Problem 744

*Reference:* [erdosproblems.com/744](https://www.erdosproblems.com/744)

For a $k$-critical graph $G$ on $n$ vertices, let $f_k(n)$ denote the minimum number of edges
that must be deleted from $G$ to make it bipartite. Erdős asked whether $f_k(n) \to \infty$ as
$n \to \infty$ for $k \ge 4$. Rödl and Tuza disproved this by showing that $f_k(n) = \binom{k-1}{2}$
for all sufficiently large $n$.

[Er81] Erdős, P.

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E.

[RoTu85] Rödl, V. and Tuza, Zs.
-/

open SimpleGraph Filter

namespace Erdos744

/-- A graph $G$ is $k$-critical if it has chromatic number exactly $k$ (i.e., is
$k$-colorable but not $(k-1)$-colorable) and every proper subgraph (strictly
fewer edges) is $(k-1)$-colorable. -/
def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.Colorable k ∧ ¬G.Colorable (k - 1) ∧
  ∀ H : SimpleGraph V, H < G → H.Colorable (k - 1)

/-- The minimum number of edges to delete from $G$ to make it bipartite
($2$-colorable). Defined as the infimum over cardinalities of edge sets
whose removal yields a $2$-colorable graph. -/
noncomputable def minEdgesToBipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (Sym2 V), S.card = m ∧
    (G.deleteEdges (↑S : Set (Sym2 V))).Colorable 2}

/-- $f_k(n)$: the minimum, over all $k$-critical graphs $G$ on $n$ vertices, of the
minimum number of edges to delete from $G$ to make it bipartite. -/
noncomputable def fk (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin n),
    IsKCritical G k ∧ minEdgesToBipartite G = m}

/--
Erdős Problem 744 (Disproved) [Er81, EHS82]:

The original conjecture asked: is it true that $f_k(n) \to \infty$ as $n \to \infty$ for $k \ge 4$?
In particular, is it true that $f_4(n) \gg \log n$?

Rödl and Tuza [RoTu85] disproved this by showing that $f_k(n) = \binom{k-1}{2}$
for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_744 : answer(False) ↔
    ∀ k : ℕ, k ≥ 4 → Tendsto (fk k) atTop atTop := by
  sorry

end Erdos744
