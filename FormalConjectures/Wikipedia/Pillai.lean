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
# Pillai's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Catalan%27s_conjecture#Pillai's_conjecture)
-/

/--
For positive integers A, B, and C, there are only finitely many solutions (x, y, m, n) to the
equation $Ax^n - By^m = C$ when (m, n) ≠ (2, 2).
-/
@[category research open, AMS 11]
theorem pillais_conjecture (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    : { (x, y, m, n) : (ℕ × ℕ × ℕ × ℕ) | (m, n) ≠ (2, 2) ∧ A * x^n - B * y^m = C }.Finite := by
  sorry
