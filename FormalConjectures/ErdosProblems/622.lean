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
# Erdős Problem 622

*Reference:* [erdosproblems.com/622](https://www.erdosproblems.com/622)

Let $G$ be a regular graph with $2n$ vertices and degree $n+1$. Must $G$ have $\gg 2^{2n}$
subsets that are spanned by a cycle?

A problem of Erdős and Faudree [Er99]. Erdős writes 'it is easy to see' that
there are at least $(1/2 + o(1))2^{2n}$ sets that are NOT on a cycle.

If the regularity condition is replaced by minimum degree $n+1$ then the answer is
no (consider $K_{n,n}$ with a spanning star in each part). Similarly this is false
with degree $n$, as $K_{n,n}$ shows.

This has been resolved by Draganić, Keevash, and Müyesser [DKM25], who prove the
asymptotically tight result that there are at least $(1/2 + o(1))2^{2n}$ subsets
which are spanned by a cycle.

[Er99] Erdős, P., *Some of my favourite problems in various branches of combinatorics*,
Le Matematiche, 1999.

[DKM25] Draganić, N., Keevash, P., Müyesser, A., *Cyclic subsets in regular Dirac graphs*,
arXiv:2503.01826 (2025).
-/

open scoped Classical
open SimpleGraph Finset

namespace Erdos622

/-- A subset $S$ of vertices is *spanned by a cycle* in $G$ if there exists
    a cycle in $G$ whose vertex set is exactly $S$. -/
def IsSpannedByCycle {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ v ∈ S, ∃ p : G.Walk v v, p.IsCycle ∧ p.support.toFinset = S

/-- The number of subsets of vertices spanned by a cycle in a graph on $2n$ vertices. -/
noncomputable def numCycleSpannedSubsets (n : ℕ)
    (G : SimpleGraph (Fin (2 * n))) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).powerset.filter (IsSpannedByCycle G)).card

/--
**Erdős Problem 622** [Er99]:

Let $G$ be a $(n+1)$-regular graph on $2n$ vertices. Then for any $\varepsilon > 0$ and
sufficiently large $n$, $G$ has at least $(1/2 - \varepsilon) \cdot 2^{2n}$ subsets that are
spanned by a cycle.

Proved by Draganić, Keevash, and Müyesser [DKM25].
-/
@[category research solved, AMS 5]
theorem erdos_622 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) →
      (numCycleSpannedSubsets n G : ℝ) ≥ (1 / 2 - ε) * (2 : ℝ) ^ (2 * n) := by
  sorry

end Erdos622
