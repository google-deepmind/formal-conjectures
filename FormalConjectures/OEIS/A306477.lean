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
# Sun's (2,4,6,8) Binomial Representation Conjecture
*Reference:* [OEIS A306477](https://oeis.org/A306477)
-/

namespace Sun2468Conjecture

/--
Zhi-Wei Sun (2019) conjectured that every positive integer n can be represented as:
n = C(w, 2) + C(x, 4) + C(y, 6) + C(z, 8) for w, x, y, z ≥ 2.

Candidate Counterexample: n* = 896,315,812,331,399.
Exhaustive computational verification over all 2,818,953,028 admissible triples
yielded no representation (Scott Sun, 2026, OSF DOI: 10.17605/OSF.IO/CAQXH).
-/
@[category research open, AMS 11 05]
theorem sun_2468_conjecture (n : ℕ) (hn : n > 0) :
    ∃ (w x y z : ℕ), w ≥ 2 ∧ x ≥ 2 ∧ y ≥ 2 ∧ z ≥ 2 ∧
    n = Nat.choose w 2 + Nat.choose x 4 + Nat.choose y 6 + Nat.choose z 8 := by
  sorry

end Sun2468Conjecture
