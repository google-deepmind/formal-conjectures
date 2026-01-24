/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Mathoverflow 100290

*Reference:* [Mathoverflow 100290](https://mathoverflow.net/a/100290)
answered by user [Timothy Chow](https://mathoverflow.net/users/3106/timothy-chow)
-/

namespace Mathoverflow100290

open_locale big_operators

/-- The n-th term of the Gourevitch series -/
def gourevitch_term (n : ℕ) : ℝ :=
  ((1 + 14 * n + 76 * n^2 + 168 * n^3) / (2^(20 * n)) : ℝ) *
  ((nat.choose (2 * n) n)^7 : ℝ)

/-- The infinite sum of the Gourevitch series -/
def gourevitch_sum : ℝ := ∑' n, gourevitch_term n

/-- Does the infinite series equal 32 / π³? -/
@[category research open, AMS 33, AMS 40, AMS 11]
theorem gourevitch_conjecture : answer(sorry) ↔ gourevitch_sum = 32 / (real.pi^3) := by
  sorry

end Mathoverflow100290
