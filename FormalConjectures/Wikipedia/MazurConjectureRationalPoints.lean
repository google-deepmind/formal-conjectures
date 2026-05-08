/-
Copyright 2025 The Formal Conjectures Authors.

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

/-
# Mazur's conjecture on the topology of rational points

In *The topology of rational points* (1992), Barry Mazur proposed that for any algebraic
variety `X` defined over `ℚ`, the topological closure of the rational points `X(ℚ)` inside
the real locus `X(ℝ)` (with its natural real-analytic topology) has only finitely many
connected components.

*References:*
 - [Mazur, *The topology of rational points*, Experimental Mathematics 1 (1992), no. 1,
    35–45.](https://projecteuclid.org/euclid.em/1048709114)
 - [Wikipedia: Mazur's conjecture](https://en.wikipedia.org/wiki/Mazur%27s_conjecture)
-/

namespace MazurRationalPoints

variable {n : ℕ} {ι : Type*}

/--
**Mazur's conjecture.**
For any finite family of rational polynomials `S : ι → MvPolynomial (Fin n) ℚ`, the closure
inside `ℝⁿ` of the set of rational solutions has only finitely many connected components.

Since `realLocus S` is closed in `ℝⁿ`, the closure is contained in the real locus, and
its components are intrinsic to `X(ℝ)`.
-/
@[category research open, AMS 11 14]
theorem mazur_conjecture
    (S : ι → MvPolynomial (Fin n) ℚ) [Finite ι] :
    Finite (ConnectedComponents (closure (rationalImage S))) := by
  sorry

end MazurRationalPoints
