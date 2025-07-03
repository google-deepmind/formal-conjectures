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
# Erdős Problem 9

*Reference:* [erdosproblems.com/9](https://www.erdosproblems.com/9)
-/

/--
The set of natural numbers that can be expressed as a prime plus two powers of 2.
-/
def Erdos9A : Set ℕ := { n | ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }

/--
Is the upper density of the set of natural numbers that can be expressed as a prime plus
two powers of 2 positive?
-/
@[category research open, AMS 5 11]
theorem erdos_9 : 0 < Erdos9A.upperDensity ↔ answer(sorry) := by
  sorry
