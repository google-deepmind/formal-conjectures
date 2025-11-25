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
# Erdős Problem 850
*Reference:* [erdosproblems.com/850](https://www.erdosproblems.com/850)
-/

namespace Erdos850

/--
Can there exist two distinct integers x and y such that x,y have the same prime factors, x+1,y+1
have the same prime factors, and x+2,y+2 also have the same prime factors?
-/
@[category research open, AMS 11]
theorem erdos_850 :
    (∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors) ↔ answer(sorry) := by
    sorry

-- TODO(Paul-Lez): formalise remaining problems

end Erdos850
