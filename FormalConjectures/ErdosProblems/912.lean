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
# Erdős Problem 912

*References:*
 - [erdosproblems.com/912](https://www.erdosproblems.com/912)
 - [Er82c] Erdős, P., Miscellaneous problems in number theory. Congr. Numer. (1982), 25-45.
-/

open scoped Nat Asymptotics
open Filter

namespace Erdos912

noncomputable def h (n : ℕ) : ℕ := (n !).factorization.frange.card

/-- Erdős and Selfridge prove in [Er82c] that `h =Θ[atTop] (fun n => (n / log n) ^ (1 / 2))`. -/
@[category research solved, AMS 11]
theorem erdos_912_theta :
    (fun n => (h n : ℝ)) =Θ[atTop] (fun n => (n / Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

/-- Prove that there exists a constant `c > 0` such that
`h ~[atTop] (fun n => c * (n / log n) ^ (1 / 2))`.
-/
@[category research open, AMS 11]
theorem erdos_912.equivalent : ∃ c > 0,
    (fun n => (h n : ℝ)) ~[atTop] (fun n => c * (n / Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

end Erdos912
