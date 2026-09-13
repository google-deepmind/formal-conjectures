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
# Erdős Problem 947

*Reference:* [erdosproblems.com/947](https://www.erdosproblems.com/947)
-/

namespace Erdos947

/-- An exact covering system: a finite collection of residue classes `a (mod n)` with distinct
positive moduli, such that every integer lies in exactly one class. -/
def IsExactCovering (s : Finset (ℤ × ℕ)) : Prop :=
  (∀ p ∈ s, 0 < p.2) ∧ (s.image Prod.snd).card = s.card ∧
    ∀ z : ℤ, ∃! p, p ∈ s ∧ z ≡ p.1 [ZMOD p.2]

/--
There is no exact covering system - that is, a finite collection of congruence classes
$a_i\pmod{n_i}$ with distinct $n_i$ such that every integer satisfies exactly one of these
congruence classes.
-/
@[category research open, AMS 11]
theorem erdos_947 : answer(sorry) ↔ ¬ ∃ s : Finset (ℤ × ℕ), IsExactCovering s := by
  sorry

end Erdos947
