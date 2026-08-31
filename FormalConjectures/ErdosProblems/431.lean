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
# Erdős Problem 431

*Reference:* [erdosproblems.com/431](https://www.erdosproblems.com/431)
-/

open scoped Pointwise

namespace Erdos431

/--
Are there two infinite sets $A$ and $B$ such that $A+B$ agrees with the set of prime numbers up to finitely many exceptions?
-/
@[category research open, AMS 11]
theorem erdos_431 :
    (∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (A + B) {p : ℕ | p.Prime}).Finite) ↔ answer(sorry) := by
  sorry

end Erdos431
