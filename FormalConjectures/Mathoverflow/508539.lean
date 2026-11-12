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

module

public import FormalConjecturesUtil

/-!
# MathOverflow 508539

Edge-vertex inequality $EV \geq 4^{n-1}$.

*References:*
- [MathOverflow 508539](https://mathoverflow.net/questions/508539), asked by
  [Paata Ivanisvili](https://mathoverflow.net/users/50901/paata-ivanisvili).
- [DIRX26] Durcik, P., Ivanisvili, P., Roos, J., and Xie, X.,
  *Sharp isoperimetric inequalities on the Hamming cube II: The critical exponent* (2026),
  [arXiv:2602.20462](https://arxiv.org/abs/2602.20462), inequality (1.2).
-/

@[expose] public section

open SimpleGraph
open scoped Finset

namespace Mathoverflow508539

/-- In the two-dimensional cube, a singleton has two crossing edges but only one vertex in
its inner boundary. -/
@[category test, AMS 5]
theorem boundaries_singleton :
    #((hypercube 2).edgeBoundary {fun _ ↦ false}) = 2 ∧
      #((hypercube 2).innerVertexBoundary {fun _ ↦ false}) = 1 := by
  decide +kernel

/-- A halfcube in dimension two attains equality: it has two crossing edges and two vertices
in its inner boundary. -/
@[category test, AMS 5]
theorem boundaries_halfcube :
    #((hypercube 2).edgeBoundary {v | v 0 = false}) = 2 ∧
      #((hypercube 2).innerVertexBoundary {v | v 0 = false}) = 2 := by
  decide +kernel

/--
For any set $A \subset \{0,1\}^n$ of half size $2^{n-1}$, we have $EV \geq 4^{n-1}$,
where $E$ denotes the edge boundary (the number of edges between $A$ and its complement), and
$V$ denotes the inner vertex boundary (the number of points in $A$ having a neighbor outside $A$).

This is the half-size case of [DIRX26, (1.2)]. The hypothesis $n > 0$ is necessary: in dimension
zero the cardinality hypothesis allows the whole cube, whose boundaries are empty.
-/
@[category research solved, AMS 5]
theorem mathoverflow_508539 {n : ℕ} (A : Finset (Fin n → Bool))
    (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) := by
  sorry

end Mathoverflow508539
