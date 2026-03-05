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

[SuVe08] Sudakov, B. and Verstraëte, J., *Cycle lengths in sparse graphs*. Combinatorica 28
(2008), 357–372.
-/

open SimpleGraph

namespace Erdos752

/-- The set of cycle lengths occurring in a simple graph. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Sudakov–Verstraëte Theorem (Erdős Problem 752)** [SuVe08]:

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
      (∀ v : V, k ≤ G.degree v) →
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → 2 * s < p.length) →
      c * (k : ℝ) ^ s ≤ ((cycleLengths G).ncard : ℝ) := by
  sorry

end Erdos752
