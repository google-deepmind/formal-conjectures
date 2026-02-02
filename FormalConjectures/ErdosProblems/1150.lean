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
# Erdős Problem 1150

*Reference:* [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
-/

open scoped Polynomial Topology

namespace Erdos1150

/--
A polynomial with coefficients in $\{-1, 1\}$.
-/
def IsPlusMinusOnePoly (P : Polynomial ℂ) : Prop :=
  ∀ i ∈ P.support, P.coeff i = 1 ∨ P.coeff i = -1

/--
The maximum modulus of a polynomial on the unit circle.
-/
noncomputable def maxModulusOnUnitCircle (P : Polynomial ℂ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖

/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
\[
  \max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?
\]

The trivial lower bound $\max_{|z|=1} |P(z)| \geq \sqrt{n+1}$ follows from Parseval's identity.
-/
@[category research open, AMS 12 30]
theorem erdos_1150 :
    answer(sorry) ↔ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : Polynomial ℂ, IsPlusMinusOnePoly P → P.natDegree = n →
        maxModulusOnUnitCircle P > (1 + c) * Real.sqrt n := by
  sorry

end Erdos1150
