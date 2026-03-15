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
# Erdős Problem 752

*Reference:* [erdosproblems.com/752](https://www.erdosproblems.com/752)

A question of Erdős, Faudree, and Schelp. Let $G$ be a graph with minimum degree $k$ and
girth $> 2s$. Must there be $\gg k^s$ many distinct cycle lengths in $G$?

Erdős, Faudree, and Schelp proved it when $s = 2$.

Sudakov and Verstraëte proved the full conjecture, and moreover showed that under the weaker
assumption of average degree $k$ and girth $> 2s$, there are $\gg k^s$ many consecutive even
integers that are cycle lengths in $G$.

Additional thanks to Raphael Steiner.

[Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) (1992), 231–240.

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is eighty,
Vol. 2 (Keszthely, 1993), 97–132.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Discrete Math. 165/166 (1997), 227–231.

[SuVe08] Sudakov, B. and Verstraëte, J., _Cycle lengths in sparse graphs_. Combinatorica 28
(2008), 357–372.
-/

open SimpleGraph

namespace Erdos752

/-- The set of cycle lengths occurring in a simple graph. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Erdős–Faudree–Schelp Conjecture (proved by Sudakov–Verstraëte)
(Erdős Problem 752)** [Er92b][Er93][Er94b][SuVe08]:

There exists an absolute constant $c > 0$ such that for every finite graph $G$
with minimum degree at least $k$ and girth greater than $2s$, the number of
distinct cycle lengths in $G$ is at least $c \cdot k^s$.
-/
@[category research solved, AMS 5]
theorem erdos_752 : answer(True) ↔
    ∃ c : ℝ, c > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (k s : ℕ),
      k ≤ G.minDegree →
      2 * s < G.girth →
      c * (k : ℝ) ^ s ≤ ((cycleLengths G).ncard : ℝ) := by
  sorry

end Erdos752
