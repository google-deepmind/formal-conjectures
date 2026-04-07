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

open Metric Set

/-!
# Bloch and Landau constants

*References:*
- [MathWorld](https://mathworld.wolfram.com/BlochConstant.html)
- [Bhowmik–Sen](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/improved-bloch-and-landau-constants-for-meromorphic-functions/FD465D1F2CEF7E8C62AFF16C3E89B7B4)
-/

/-- The **Bloch radius** $B_f$ of a function $f$ is the radius of the largest univalent disk in the
image of the unit disk under $f$. -/
noncomputable def blochRadius (f : ℂ → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ S ⊆ ball 0 1, ∃ x, ball x r ⊆ f '' S ∧ InjOn f S}

/-- The **Landau radius** $L_f$ of a function $f$ is the radius of the largest disk in the image of
the unit disk under $f$. -/
noncomputable def landauRadius (f : ℂ → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x, ball x r ⊆ f '' (ball 0 1)}

/-- The **Bloch constant** $B$ is the infimum of the Bloch radius over all functions holomorphic
in the unit disk such that `deriv f 0 = 1`. -/
noncomputable def blochConstant : ℝ :=
  iInf (fun f : {f : ℂ → ℂ // DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1} => blochRadius f.1)

/-- The **Landau constant** $L$ is the infimum of the Landau radius over all functions holomorphic
in the unit disk such that `deriv f 0 = 1`. -/
noncomputable def landauConstant : ℝ :=
  iInf (fun f : {f : ℂ → ℂ // DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1} => landauRadius f.1)

@[category research solved, AMS 30]
theorem blochConstant_lower_bound : Real.sqrt 3 / 4 + 2 * 10 ^ (-4 : ℤ) ≤ blochConstant := by
  sorry

@[category research solved, AMS 30]
theorem blochConstant_upper_bound :
    blochConstant ≤ Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
    (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) := by
  sorry

/-- Ahlfors and Grunsky conjectured that this upper bound is the precise value of the Bloch
constant. -/
@[category research open, AMS 30]
theorem blochConstant_exact_value :
    blochConstant = Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
    (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) := by
  sorry

@[category research solved, AMS 30]
theorem landauConstant_lower_bound : 0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant := by
  sorry

@[category research solved, AMS 30]
theorem landauConstant_upper_bound :
    landauConstant ≤ Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry

/-- Rademacher conjectured that this upper bound is the precise value of the Landau constant. -/
@[category research open, AMS 30]
theorem landauConstant_exact_value :
    landauConstant = Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry
