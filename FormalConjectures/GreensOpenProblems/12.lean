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
# Green's Open Problem 12

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.12)
-/

namespace Green12

open Finset

/--
Let $G$ be an abelian group of size $N$, and suppose that $A \subset G$ has density $\alpha$.
Are there at least $\alpha^{15} N^{10}$ tuples $(x_1, \dots, x_5, y_1, \dots, y_5) \in G^{10}$
such that $x_i + y_j \in A$ whenever $j \in \{i, i+1, i+2\}$?

Note: We interpret indices modulo 5.
-/
@[category research open, AMS 5 11]
theorem green_12 : answer(sorry) ↔
    ∀ {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G],
    ∀ (A : Finset G),
    let N := Fintype.card G
    let α := (A.card : ℝ) / N
    let valid_tuples : Finset ((Fin 5 → G) × (Fin 5 → G)) := Finset.univ.filter (fun t =>
      ∀ i : Fin 5, ∀ j ∈ ({i, i + 1, i + 2} : Finset (Fin 5)), t.1 i + t.2 j ∈ A)
    (valid_tuples.card : ℝ) ≥ α ^ 15 * (N : ℝ) ^ 10 := by
  sorry

end Green12
