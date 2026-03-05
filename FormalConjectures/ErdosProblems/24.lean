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
# Erdős Problem 24

*Reference:* [erdosproblems.com/24](https://www.erdosproblems.com/24)

Every triangle-free graph on $5n$ vertices contains at most $n^5$ copies of $C_5$.
Proved independently by Grzesik [Gr12] and by Hatami, Hladký, Král, Norine, and
Razborov [HHKNR13].

[Gr12] Grzesik, A., _On the maximum number of five-cycles in a triangle-free graph_.
Journal of Combinatorial Theory, Series B (2012), 1061-1066.

[HHKNR13] Hatami, H., Hladký, J., Král, D., Norine, S., and Razborov, A.,
_On the number of pentagons in triangle-free graphs_.
Journal of Combinatorial Theory, Series A (2013), 722-732.
-/

open SimpleGraph Finset

namespace Erdos24

/--
Every triangle-free graph on $5n$ vertices contains at most $n^5$ copies of $C_5$.

We count labeled $5$-cycles: injective functions $f : \text{Fin}\,5 \to \text{Fin}(5n)$ such
that $f(i)$ is adjacent to $f(i+1 \bmod 5)$ for all $i$. Each unordered $C_5$ yields exactly
$10$ labeled $5$-cycles ($5$ rotations $\times$ $2$ reflections), so the labeled count bound
is $10 \cdot n^5$.

Proved independently by Grzesik [Gr12] and by Hatami, Hladký, Král, Norine, and
Razborov [HHKNR13].
-/
@[category research solved, AMS 5]
theorem erdos_24 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    (Finset.univ.filter (fun (f : Fin 5 → Fin (5 * n)) =>
      Function.Injective f ∧
      ∀ i : Fin 5, G.Adj (f i) (f (i + 1)))).card
    ≤ 10 * n ^ 5 := by
  sorry

end Erdos24
