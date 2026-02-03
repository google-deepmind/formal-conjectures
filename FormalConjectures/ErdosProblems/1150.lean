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

open scoped Polynomial

namespace Erdos1150

/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
$$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$
-/
@[category research open, AMS 12 30]
theorem erdos_1150 :
    answer(sorry) ↔ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n := by
  sorry

/--
The trivial lower bound from Parseval's identity: for any polynomial $P$ of degree $n$ with
coefficients in $\{-1, 1\}$, we have $\max_{|z|=1} |P(z)| \geq \sqrt{n+1}$.

This follows from Parseval's identity:
$$\frac{1}{2\pi} \int_0^{2\pi} |P(e^{i\theta})|^2 d\theta = \sum_{k=0}^{n} |a_k|^2 = n+1$$
since each $|a_k|^2 = 1$.
-/
@[category graduate, AMS 12 30]
theorem erdos_1150.parseval_lower_bound (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  sorry

end Erdos1150
