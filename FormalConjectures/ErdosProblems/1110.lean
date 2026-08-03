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

import FormalConjectures.ErdosProblems.«246»

/-!
# Erdős Problem 1110

Let `p > q ≥ 2` be coprime. A natural number is representable when it is a sum
of terms `p^k * q^l` such that no selected term divides another selected term.
The open problem asks, outside the exceptional pair `{2, 3}`, whether infinitely
many non-representable numbers are coprime to `p * q`.

*Reference:* [Erdős Problem 1110](https://www.erdosproblems.com/1110)
-/

namespace Erdos1110

/-- A finite set is an antichain for divisibility. -/
def IsDvdAntichain (s : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ s → b ∈ s → a ∣ b → a = b

/--
`n` is representable with respect to `p` and `q` if it is the sum of a finite
divisibility antichain of terms of the form `p^k * q^l`.
-/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ Erdos246.Gamma p q ∧
    IsDvdAntichain s ∧
    s.sum id = n

/-- A number coprime to `p * q` which is not representable. -/
def IsCoprimeNonrepresentable (p q n : ℕ) : Prop :=
  Nat.Coprime n (p * q) ∧ ¬Representable p q n

/--
**Erdős Problem 1110.**

For coprime `p > q ≥ 2`, outside the exceptional pair `(3, 2)`, are there
infinitely many non-representable natural numbers coprime to `p * q`?
-/
@[category research open, AMS 5 11]
theorem erdos_1110 (p q : ℕ) (hpq : q < p) (hq : 2 ≤ q)
    (hcoprime : Nat.Coprime p q) (hexceptional : ¬(p = 3 ∧ q = 2)) :
    Set.Infinite {n : ℕ | IsCoprimeNonrepresentable p q n} := by
  sorry

end Erdos1110
