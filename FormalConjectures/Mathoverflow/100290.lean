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
# Mathoverflow 100290

*Reference:* [Mathoverflow 100290](https://mathoverflow.net/a/100290)
answered by user [Timothy Chow](https://mathoverflow.net/users/3106/timothy-chow)
-/

namespace Mathoverflow100290

open scoped BigOperators

/-- The n-th term of the Gourevitch series -/
noncomputable def gourevitch_term (n : ℕ) : ℝ :=
  ((1 + 14 * n + 76 * n ^ 2 + 168 * n ^ 3) / (2 ^ (20 * n)) : ℝ) * ((Nat.central_binom n : ℝ) ^ 7)

/-- The infinite sum of the Gourevitch series -/
noncomputable def gourevitch_sum : ℝ := ∑' n, gourevitch_term n

/-- Does the infinite series equal 32 / π³? -/
@[category research open, AMS 11 33 40]
theorem gourevitch_conjecture : answer(sorry) ↔ gourevitch_sum = 32 / (Real.pi^3) := by
  sorry

end Mathoverflow100290
