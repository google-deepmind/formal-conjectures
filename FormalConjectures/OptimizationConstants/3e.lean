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
# Tao's Optimization Constant 3e / Unnormalized single-set sum-difference exponent

*References:*
- [Tao's Optimization Constant 3e](https://teorth.github.io/optimizationproblems/constants/3e.html)
- [FP1973] Freiman, G. A.; Pigaev, V. P., *The relation between the invariants R and T*.
  Kalinin. Gos. Univ. (1973), 172–174.
- [HRY1999] Hennecart, F.; Robert, G.; Yudin, A., *On the number of sums and differences*.
  Astérisque 258 (1999), 173–178.
- [GHR2007] Gyarmati, K.; Hennecart, F.; Ruzsa, I. Z., *Sums and differences of finite sets*.
  Functiones et Approximatio Commentarii Mathematici 37 (2007), 175–186.
- [R1996] Ruzsa, I. Z., *Sums of finite sets*. Number Theory: New York Seminar,
  Springer (1996), 281–293.
-/

namespace Constant3e

open scoped Pointwise

/-- **Tao's Optimization Constant 3e / Unnormalized single-set sum-difference exponent**. -/
noncomputable def C3e : ℝ :=
  sSup {Real.log (A - A).card / Real.log (A + A).card | A : Finset ℤ}

@[category API, AMS 5 11]
theorem logRatio_le (A : Finset ℤ) :
    (Real.log (A - A).card / Real.log (A + A).card) ≤ C3e := by
  sorry -- needs an upper bound

/-- The trivial lower bound, implied by arithmetic progressions. -/
@[category textbook, AMS 5 11]
theorem c3e_ge_1 : 1 ≤ C3e := by
  sorry

/-- The current best known lower bound, due to Hennecart, Robert and Yudin [HRY1999].
It comes from high-dimensional simplices projected to the integers [GHR2007]. -/
@[category research solved, AMS 5 11]
theorem c3e_lower_bound :
    (Real.log (1 + Real.sqrt 2) / Real.log 2) ≤ C3e := by
  sorry

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 5 11]
theorem c3e_lower_bound_improved : answer(sorry) ↔
    (Real.log (1 + Real.sqrt 2) / Real.log 2) < C3e := by
  sorry

/-- The first recorded upper bound, obtained from Ruzsa’s triangle inequality [R1996]
and the elementary estimate $|A+A|\le |A|^2$. -/
@[category textbook, AMS 5 11]
theorem c3e_le_3_div_2 : C3e ≤ 3 / 2 := by
  sorry

/-- The current best known upper bound, due to Freiman and Pigaev [FP1973]. Their cardinality
inequality bounds the difference set by the sumset to the power $4/3$. -/
@[category research solved, AMS 5 11]
theorem c3e_upper_bound : C3e ≤ 4 / 3 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 5 11]
theorem c3e_upper_bound_improved : answer(sorry) ↔ C3e < 4 / 3 := by
  sorry

end Constant3e
