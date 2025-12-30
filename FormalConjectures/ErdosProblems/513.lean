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

/-!
# Erdős Problem 513

*Reference:*
 - [erdosproblems.com/513](https://www.erdosproblems.com/513)
 - [ClHa64] Clunie, J. and Hayman, W. K., The maximum term of a power series. J. Analyse Math.
  (1964), 143-186.
-/

open scoped Nat Real
open Filter

namespace Erdos513

noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨆ n, ‖iteratedDeriv n f 0 * (n ! : ℝ)⁻¹ * r ^ n‖) / (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖)

/-- Let `f` be a transcendental entire function. What is the greatest possible value of
`liminf (fun r : ℝ => ratio r f) atTop`? -/
@[category research open, AMS 30]
theorem erdos_513.sup : answer(sorry) = ⨆ f : {f : ℂ → ℂ // IsTranscendental f},
    (liminf (fun r : ℝ => ratio r f) atTop) := by
  sorry

/-- For all transcendental entire function `f`, `liminf (fun r : ℝ => ratio r f) atTop ≤ 2 / π - c`
for some `c > 0`. This is proved in [ClHa64]. -/
@[category research solved, AMS 30]
theorem erdos_513.upper_bound : ∃ c > 0, ⨆ f : {f : ℂ → ℂ // IsTranscendental f},
    (liminf (fun r : ℝ => ratio r f) atTop) ≤ 2 / π - c :=
  sorry

/-- For all transcendental entire function `f`, `liminf (fun r : ℝ => ratio r f) atTop > 1 / 2`. -/
@[category research solved, AMS 30]
theorem erdos_513.lower_bound : ⨆ f : {f : ℂ → ℂ // IsTranscendental f},
    (liminf (fun r : ℝ => ratio r f) atTop) > 1 / 2 :=
  sorry

end Erdos513
