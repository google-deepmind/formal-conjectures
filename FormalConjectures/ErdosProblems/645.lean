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
# Erdős Problem 645

*Reference:* [erdosproblems.com/645](https://www.erdosproblems.com/645)
-/


namespace Erdos645

/--
If ℕ is $2$-coloured then there must exist a monochromatic three-term arithmetic progression
$x,x+d,x+2d$ such that $d>x$.
-/
@[category research solved, AMS 5 11]
theorem erdos_645 (c : ℕ → Bool) : ∃ x d, 0 < x ∧ x < d ∧
    (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) := by
  sorry

end Erdos645
