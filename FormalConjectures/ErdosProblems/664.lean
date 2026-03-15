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
# Erdős Problem 664

*Reference:* [erdosproblems.com/664](https://www.erdosproblems.com/664)

Let $c < 1$ be some constant and $A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ be such that
$|A_i| > c\sqrt{n}$ for all $i$ and $|A_i \cap A_j| \leq 1$ for all $i \neq j$.

Must there exist some set $B$ such that $B \cap A_i \neq \emptyset$ and
$|B \cap A_i| \ll_c 1$ for all $i$?

This was disproved by Alon, who showed that for $c = 2/5$ and appropriate families derived
from random subsets of lines of a projective plane, any transversal $B$ must intersect
some $A_j$ in $\Omega(\log n)$ points.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica 1 (1981), 25–42.

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
number theory_ (1997).

See also: Erdős Problem 1159 for the weaker projective plane variant.
-/

open Finset

namespace Erdos664

/--
Erdős Problem 664 (Disproved) [Er81][Er97f]:

Let $c < 1$ be some constant and $A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ with
$|A_i| > c\sqrt{n}$ for all $i$ and $|A_i \cap A_j| \leq 1$ for $i \neq j$. Must there
exist a transversal $B$ (meeting every $A_i$) such that $|B \cap A_i| \leq K$ for all $i$,
where $K$ depends only on $c$?

Disproved by Alon using random subsets of lines of a projective plane, with $c = 2/5$.
-/
@[category research solved, AMS 5]
theorem erdos_664 : answer(False) ↔
    ∀ c : ℝ, 0 < c → c < 1 →
    ∃ K : ℕ, ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
      (∀ i, (↑(A i).card : ℝ) > c * Real.sqrt ↑n) →
      (∀ i j, i ≠ j → ((A i) ∩ (A j)).card ≤ 1) →
      ∃ B : Finset (Fin n),
        (∀ i, ((A i) ∩ B).Nonempty) ∧
        (∀ i, ((A i) ∩ B).card ≤ K) := by
  sorry

end Erdos664
