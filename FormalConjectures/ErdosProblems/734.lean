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
# Erdős Problem 734

*Reference:* [erdosproblems.com/734](https://www.erdosproblems.com/734)

Find, for all large $n$, a non-trivial pairwise balanced block design
$A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ such that, for all $t$,
there are $O(n^{1/2})$ many $i$ such that $|A_i| = t$.

A pairwise balanced block design (PBBD) on $\{1, \ldots, n\}$ is a
collection of subsets such that every pair of distinct elements is
contained in exactly one block.

Erdős and de Bruijn proved that any PBBD has $m \geq n$ blocks, which
implies there must be some block size $t$ appearing at least
$\Omega(\sqrt{n})$ times. This conjecture asks whether $O(\sqrt{n})$ is
achievable for every block size simultaneously.

[Er81] Erdős, P., _Problems and results in graph theory and combinatorics_,
Proceedings of the Southeastern Conference on Combinatorics, Graph Theory,
and Computing (1981), p. 35.
-/

open Finset

namespace Erdos734

/-- A pairwise balanced block design (PBBD) on `Fin n`: a collection of
subsets such that every pair of distinct elements is contained in
exactly one block. -/
def IsPBBD (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  ∀ (a b : Fin n), a ≠ b →
    (blocks.filter (fun B => a ∈ B ∧ b ∈ B)).card = 1

/--
Erdős Problem 734 [Er81, p.35]:

For all sufficiently large $n$, there exists a non-trivial pairwise balanced
block design on $\{1, \ldots, n\}$ where for every $t$, at most $O(\sqrt{n})$
blocks have size $t$. Non-trivial means at least one block has size $\geq 3$.
-/
@[category research open, AMS 5]
theorem erdos_734 :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ blocks : Finset (Finset (Fin n)),
        IsPBBD n blocks ∧
        (∃ B ∈ blocks, 2 < B.card) ∧
        ∀ t : ℕ, ((blocks.filter (fun B => B.card = t)).card : ℝ) ≤
          C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos734
