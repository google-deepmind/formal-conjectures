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
# Erdős Problem 816

*Reference:* [erdosproblems.com/816](https://www.erdosproblems.com/816)

Let $G$ be a graph with $2n+1$ vertices and $n^2+n+1$ edges. Must $G$ contain two
vertices of the same degree which are joined by a path of length $3$?

A problem of Erdős and Hajnal. The example of $K_{n,n+1}$ shows that this fails
if we only have $n^2+n$ edges.

This was proved by Chen and Ma [ChMa25], who showed the stronger statement that,
provided $n \geq 600$, all graphs with $2n+1$ vertices and at least $n^2+n$ edges
contain two vertices of the same degree joined by a path of length $3$, except
$K_{n,n+1}$.
-/

open SimpleGraph

namespace Erdos816

/--
**Erdős Problem 816** (proved by Chen–Ma [ChMa25]):

For every $n$, every graph on $2n+1$ vertices with $n^2+n+1$ edges contains
two vertices of the same degree joined by a path of length $3$.
-/
@[category research solved, AMS 5]
theorem erdos_816 : answer(True) ↔
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin (2 * n + 1)),
      G.edgeSet.ncard = n ^ 2 + n + 1 →
        ∃ v w : Fin (2 * n + 1), v ≠ w ∧
          (G.neighborSet v).ncard = (G.neighborSet w).ncard ∧
          ∃ p : G.Walk v w, p.IsPath ∧ p.length = 3 := by
  sorry

end Erdos816
