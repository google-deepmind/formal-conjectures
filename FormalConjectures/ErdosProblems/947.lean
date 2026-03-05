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
# Erdős Problem 947

There is no exact covering system — that is, a finite collection of congruence classes
$a_i \pmod{n_i}$ with distinct moduli $n_i \geq 2$ such that every integer belongs to
exactly one of these congruence classes. This was proved independently by
Mirsky–Newman and Davenport–Rado.

*Reference:* [erdosproblems.com/947](https://www.erdosproblems.com/947)
-/

namespace Erdos947

/--
There is no exact covering system with distinct moduli.
That is, there is no finite collection of congruence classes $a_i \pmod{n_i}$ with
distinct moduli $n_i \geq 2$ such that every integer belongs to exactly one of
these congruence classes.

This was proved independently by Mirsky-Newman and Davenport-Rado.
-/
@[category research solved, AMS 11]
theorem erdos_947 :
    ¬ ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      (∀ i, 2 ≤ n i) ∧
      (Function.Injective n) ∧
      (∀ x : ℤ, ∃! i : Fin k, (↑(n i) : ℤ) ∣ (x - a i)) := by
  sorry

end Erdos947
