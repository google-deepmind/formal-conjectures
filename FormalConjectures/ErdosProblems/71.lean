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
# Erdős Problem 71

*References:*
- [erdosproblems.com/71](https://www.erdosproblems.com/71)
- [Bo77] Bollobás, Béla, *Cycles modulo $k$*. Bull. London Math. Soc. (1977), 97-98.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
-/

namespace Erdos71

/--
Is it true that for every infinite arithmetic progression $P$ which contains even numbers
there is some constant $c=c(P)$ such that every graph with average degree at least $c$
contains a cycle whose length is in $P$?

In [Er82e] Erdős credits this conjecture to himself and Burr. This has been proved by
Bollobás [Bo77]. The best dependence of the constant $c(P)$ is unknown.

The infinite arithmetic progression is encoded as a set $P \subseteq \mathbb{N}$ satisfying
`P.IsAPOfLength ⊤` (which forces a positive common difference), and "contains even numbers"
as the existence of an even element. The average degree of a finite simple graph is
`SimpleGraph.averageDegree`, i.e. $(\sum_v \deg v)/|V| \in \mathbb{Q}$, and a cycle whose
length is in $P$ is a cycle walk `w` with `w.length ∈ P`.
-/
@[category research solved, AMS 5]
theorem erdos_71 : answer(True) ↔
    ∀ P : Set ℕ, P.IsAPOfLength ⊤ → (∃ n ∈ P, Even n) →
      ∃ c : ℚ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj], c ≤ G.averageDegree →
          ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length ∈ P := by
  sorry

end Erdos71
