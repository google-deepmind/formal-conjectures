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
# Erdős Problem 895

Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph
on $\{1, \ldots, n\}$ then there must exist an independent set $\{a, b, a+b\}$?

*Reference:* [erdosproblems.com/895](https://www.erdosproblems.com/895)

[Er95d] Erdős, P. and Hajnal, A., unpublished (1995).
-/

open SimpleGraph

namespace Erdos895

/--
Erdős Problem 895 [Er95d]:

Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph
on $\{1, \ldots, n\}$ then there exist distinct $a, b$ with $a + b$ also in the vertex set
such that $\{a, b, a+b\}$ is an independent set in $G$?

Proved by Barber using a SAT solver: this is true for all $n \geq 18$.

We model the vertex set as $\operatorname{Fin} n = \{0, \ldots, n-1\}$ and require $a \geq 1$,
$b \geq 1$, and $a + b < n$ so that $a$, $b$, $a+b$ are all valid vertices
representing positive integers with $a + b$ in range.
-/
@[category research solved, AMS 5]
theorem erdos_895 : answer(True) ↔
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    ∃ a b : Fin n,
      a ≠ b ∧ a.val ≥ 1 ∧ b.val ≥ 1 ∧
      ∃ h : a.val + b.val < n,
        ¬G.Adj a b ∧
        ¬G.Adj a ⟨a.val + b.val, h⟩ ∧
        ¬G.Adj b ⟨a.val + b.val, h⟩ := by
  sorry

end Erdos895
