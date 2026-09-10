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

import FormalConjecturesUtil

/-!
# The Hodge Conjecture

Let $X$ be a nonsingular complex projective variety and let $p$ be a natural number. The Hodge
conjecture asserts that every rational Hodge class of degree $2p$ on $X$ is a rational linear
combination of the classes of algebraic subvarieties of $X$ of codimension $p$. It is one of the
seven Millennium Prize Problems posed by the Clay Mathematics Institute.

The background material used by this statement lives in `FormalConjecturesForMathlib`. In
particular `Hdg^p(ℚ; X)` is the space of rational Hodge classes of codimension $p$, defined in
`FormalConjecturesForMathlib.AlgebraicGeometry.HodgeFiltration`, and `algebraicCycleClassSpan X p`
is the rational span of the constructed codimension-$p$ component classes, defined in
`FormalConjecturesForMathlib.AlgebraicGeometry.Coniveau`. A variety is presented here as an
object `X` of `Over (Spec ↧ℂ)`, so that $X$ itself is `X.left` and its structure morphism is
`X.hom`.

## TODO

The conjecture is currently stated using the rational span of the constructed component classes,
which are the values of the constructed cycle-class map on individual components. Once that map is
proved to kill principal-divisor relations, it should be descended to the rational Chow group.
After separately proving that its values are Hodge classes, the conjecture can equivalently be
restated as surjectivity onto the rational Hodge classes.

*References:*
- [P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
- [Wikipedia](https://en.wikipedia.org/wiki/Hodge_conjecture)
-/

namespace HodgeConjecture

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- The **Hodge conjecture**: is it true that, for every nonsingular complex projective variety
$X$ and every natural number $p$, every rational Hodge class of degree $2p$ on $X$ is a rational
linear combination of the classes of algebraic subvarieties of $X$ of codimension $p$?

The algebraic subspace is the span of the actual constructed component classes, not a subspace
defined by quantifying over generators of a supported-cohomology image. -/
@[category research open, AMS 14 32]
theorem hodge_conjecture : answer(sorry) ↔
    ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
      Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p := by
  sorry

end HodgeConjecture
