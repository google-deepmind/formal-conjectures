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

*Reference:* [erdosproblems.com/71](https://www.erdosproblems.com/71)

For every infinite arithmetic progression containing even numbers, there exists $c > 0$
such that every graph with average degree at least $c$ contains a cycle whose length
belongs to the progression. Credited to Erdős and Burr [Er82e]. Proved by Bollobás [Bo77].

See also Problem 72.

[Bo77] Bollobás, B., _Cycles modulo k_. Bull. London Math. Soc. **9** (1977), 97–98.
[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_.
L'Enseignement Math. **27** (1982), 163–176.
[Er95] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. **164** (1997), 81–85.
[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_.
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).
-/

open SimpleGraph

namespace Erdos71

/--
Erdős Problem #71 (credited to Erdős and Burr [Er82e], proved by Bollobás [Bo77]):
For every infinite arithmetic progression $P = \{a, a+d, a+2d, \ldots\}$ (with $d \geq 1$)
that contains even numbers, there exists a constant $c = c(P) > 0$ such that every
finite graph with average degree at least $c$ contains a cycle whose length belongs to $P$.

The average degree of a graph $G$ on $n > 0$ vertices is $2|E(G)|/n$.
-/
@[category research solved, AMS 5]
theorem erdos_71 (a d : ℕ) (hd : 1 ≤ d) (heven : ∃ k : ℕ, Even (a + k * d)) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        0 < Fintype.card V →
        c ≤ (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card V : ℝ) →
        ∃ m : ℕ, (∃ k : ℕ, m = a + k * d) ∧
          ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m := by
  sorry

end Erdos71
