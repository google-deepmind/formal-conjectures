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
variety `X` defined over `ℚ` — that is, any reduced scheme of finite type over `Spec ℚ` —
the topological closure of the rational points `X(ℚ)` inside the real points `X(ℝ)`
(with its natural real-analytic topology) has only finitely many connected components.

*References:*
 - [Mazur, *The topology of rational points*, Experimental Mathematics 1 (1992), no. 1,
    35–45.](https://projecteuclid.org/euclid.em/1048709114)
 - [Wikipedia: Mazur's conjecture](https://en.wikipedia.org/wiki/Mazur%27s_conjecture)
-/

namespace MazurRationalPoints

universe u

open AlgebraicGeometry CategoryTheory

/--
**Mazur's conjecture.**
For any reduced scheme `X` of finite type over `Spec ℚ`, the closure of the image of the
rational points `X(ℚ)` inside the real points `X(ℝ)` (with its natural real-analytic
topology) has only finitely many connected components.

The topology on `X(ℝ) = Points ℚ ℝ X` is the canonical real-analytic topology supplied by
`Points.instTopologicalSpace`: the final topology induced by the inclusions
`Points ℚ ℝ U.toScheme ↪ Points ℚ ℝ X` for every affine open `U ⊆ X`, where each
`Points ℚ ℝ U.toScheme` carries the topology of pointwise convergence on
`Γ(U.toScheme, ⊤) ⟶ ℝ`. -/
@[category research open, AMS 11 14]
theorem mazur_conjecture
    (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of ℚ))] [IsAlgebraicVariety ℚ X] :
    Finite (ConnectedComponents (closure (Set.range (Points.ofRat (X := X) ℚ ℝ)))) := by
  sorry

end MazurRationalPoints
