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
# Mathoverflow 508539

Edge-vertex inequality $EV ≥ 4^(n-1)$

*References:*
 - [mathoverflow/508539](https://mathoverflow.net/questions/508539)
asked by user [*Paata Ivanisvili*](https://mathoverflow.net/users/50901/paata-ivanisvili)
 - [arXiv:2602.20462](https://arxiv.org/abs/2602.20462)
-/

open Classical SimpleGraph Finset symmDiff
open scoped SimpleGraph

namespace Mathoverflow508539

variable {n : ℕ}

/-- The edge boundary of a set `A` of vertices in the hypercube graph `Hypercube n` is the number
of ordered pairs `(a, b)` where `a ∈ A`, `b ∉ A`, and `a` and `b` are adjacent. -/
noncomputable def edgeBoundary (A : Finset (Finset (Fin n))) : ℕ :=
  ((A ×ˢ Aᶜ).filter (fun p : Finset (Fin n) × Finset (Fin n) =>
    (Q(n)).Adj p.1 p.2)).card

/-- The inner vertex boundary of a set `A` of vertices in the hypercube graph `Hypercube n` is
the number of vertices in `A` that have at least one neighbor outside `A`. -/
noncomputable def innerVertexBoundary (A : Finset (Finset (Fin n))) : ℕ :=
  (A.filter (fun v => ∃ w ∈ Aᶜ, (Q(n)).Adj v w)).card

/--
For any set $A \subset \{0,1\}^n$ of half size $2^{n-1}$, we have $E \cdot V \geq 4^{n-1}$,
where $E$ is the edge boundary (number of edges between $A$ and its complement) and $V$ is
the inner vertex boundary (number of vertices in $A$ with at least one neighbor outside $A$).

This inequality follows from a corollary in ([arXiv:2602.20462](https://arxiv.org/abs/2602.20462)).
However, the proof relies on constructing a rather sophisticated Bellman function and then
verifying a collection of delicate inequalities using interval arithmetic.
-/
@[category research solved, AMS 5]
theorem mathoverflow_508539 (A : Finset (Finset (Fin n)))
    (hA : A.card = 2 ^ (n - 1)) (hn : 0 < n):
    4 ^ (n - 1) ≤ edgeBoundary A * innerVertexBoundary A := by
  sorry

end Mathoverflow508539
