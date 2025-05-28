/-
Copyright 2025 Google LLC

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
# Goldbach’s Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture)
-/

/--
Goldbach’s conjecture: every even integer greater than 2 can be written
as the sum of two prime numbers.
-/
@[category research open, AMS 11]
theorem goldbach (n : ℕ) (h₁: 2 < n) (h₂ : n % 2 = 0) :
  ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n := by
  sorry
