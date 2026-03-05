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
# Erdős Problem 599

*Reference:* [erdosproblems.com/599](https://www.erdosproblems.com/599)

Sometimes known as the Erdős-Menger conjecture. Let $G$ be a (possibly infinite)
graph and $A$, $B$ be disjoint independent sets of vertices. Must there exist a
family $P$ of disjoint paths between $A$ and $B$ and a set $S$ which contains
exactly one vertex from each path in $P$, and such that every path between $A$
and $B$ contains at least one vertex from $S$?

When $G$ is finite this is equivalent to Menger's theorem. Erdős was interested
in the case when $G$ is infinite. This was proved by Aharoni and Berger [AhBe09].

[Er81] Erdős, P. (1981).

[Er87] Erdős, P. (1987).

[AhBe09] Aharoni, R. and Berger, E., _Menger's theorem for infinite graphs_.
Inventiones Mathematicae 176 (2009), 1-62.
-/

open SimpleGraph

namespace Erdos599

/--
Erdős Problem 599 (Erdős-Menger Conjecture) [Er81][Er87]:

For any graph $G$ and disjoint independent sets $A$, $B$, there exists a family of
pairwise vertex-disjoint $A$-$B$ paths and a set $S$ containing exactly one vertex
from each path, such that $S$ separates $A$ from $B$ (every $A$-$B$ walk meets $S$).
-/
@[category research solved, AMS 5]
theorem erdos_599 : answer(True) ↔
    ∀ (V : Type*) (G : SimpleGraph V) (A B : Set V),
      Disjoint A B →
      (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) →
      (∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v) →
      ∃ (ι : Type) (src : ι → V) (dst : ι → V)
        (p : (i : ι) → G.Walk (src i) (dst i))
        (S : Set V),
        (∀ i, src i ∈ A) ∧
        (∀ i, dst i ∈ B) ∧
        (∀ i, (p i).IsPath) ∧
        (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) ∧
        (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
        (∀ (x : V) (y : V), x ∈ A → y ∈ B →
          ∀ (w : G.Walk x y), ∃ s ∈ S, s ∈ w.support) := by
  sorry

end Erdos599
