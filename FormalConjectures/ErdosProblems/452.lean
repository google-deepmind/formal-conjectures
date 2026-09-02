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
# Erdős Problem 452

*Reference:* [erdosproblems.com/452](https://www.erdosproblems.com/452)
-/

namespace Erdos452

open scoped ArithmeticFunction.omega

/-- The greatest length of an interval in $[x,2x]$ on which
$\omega(n) > \log\log n$ everywhere. -/
noncomputable def largeOmegaIntervalLength (x : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun len ↦ ∃ start, x ≤ start ∧ start + len ≤ 2 * x + 1 ∧
      ∀ n ∈ Finset.Ico start (start + len),
        Real.log (Real.log (n : ℝ)) < (ω n : ℝ))
    (x + 1)

/-- Determine the largest length of an interval in $[x,2x]$ on which
$\omega(n) > \log\log n$ everywhere. -/
@[category research open, AMS 11]
theorem erdos_452 : largeOmegaIntervalLength = answer(sorry) := by
  sorry

end Erdos452
