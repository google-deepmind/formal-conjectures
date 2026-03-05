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
# Erdős Problem 754

*Reference:* [erdosproblems.com/754](https://www.erdosproblems.com/754)

Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^4$
in which every $x \in A$ has at least $f(n)$ points in $A$ equidistant from $x$.

Is it true that $f(n) \leq n/2 + O(1)$?

Avis, Erdős, and Pach [AEP88] proved that $n/2 + 2 \leq f(n) \leq (1 + o(1))n/2$.
This was proved by Swanepoel [Sw13].

[Er94b] Erdős, P., *Some old and new problems on combinatorial geometry*.

[AEP88] Avis, D., Erdős, P., and Pach, J.

[Sw13] Swanepoel, K.J.
-/

open Classical

namespace Erdos754

/--
**Erdős Problem 754** [Er94b]:

Let $f(n)$ be the largest $k$ such that there exists a set $A$ of $n$ points in $\mathbb{R}^4$
where every $x \in A$ has at least $k$ other points in $A$ all at the same distance
from $x$. Is it true that $f(n) \leq n/2 + O(1)$?

Formulated as: there exists a constant $C$ such that for every finite set
$A \subseteq \mathbb{R}^4$ of $n$ points, if every point $x \in A$ has at least $k$ other
points at a common distance from $x$, then $k \leq n/2 + C$.
-/
@[category research solved, AMS 52]
theorem erdos_754 :
    answer(True) ↔
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 4)),
      A.card = n →
      ∀ k : ℕ,
        (∀ x ∈ A, ∃ d : ℝ,
          k ≤ (A.filter (fun y => x ≠ y ∧ dist x y = d)).card) →
        (k : ℝ) ≤ n / 2 + C := by
  sorry

end Erdos754
