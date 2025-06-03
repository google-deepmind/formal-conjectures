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
# Oppermann's Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Oppermann%27s_conjecture)
-/

/--
For every integer `x ≥ 2` there exists a prime between `x(x-1)` and `x²`.
-/
@[category research open, AMS 11]
theorem oppermann_conjecture.parts.i (x : ℕ) (hx : x ≥ 2) :
  ∃ p ∈ Finset.Ioo (x * (x - 1)) (x^2), Prime p := by
  sorry

/--
For every integer `x ≥ 2` there exists a prime between `x²` and `x(x+1)`.
-/
@[category research open, AMS 11]
theorem oppermann_conjecture.parts.ii (x : ℕ) (hx : x ≥ 2) :
  ∃ p ∈ Finset.Ioo (x^2) (x * (x + 1)), Prime p := by
  sorry
