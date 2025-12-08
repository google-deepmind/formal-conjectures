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
# Erdős Problem 1108

*Reference:* [erdosproblems.com/1108](https://www.erdosproblems.com/1108)
-/

open Nat Filter

namespace Erdos1108

/--
The set $A = \left\{ \sum_{n\in S}n! : S\subset \mathbb{N}\text{ finite}\right\}$ of all finite
sums of distinct factorials.
-/
def FactorialSums : Set ℕ :=
  { m : ℕ | ∃ S : Finset ℕ, m = S.sum (fun n => Nat.factorial n) }

/--
A number is powerful if each prime factor appears with exponent at least 2.
-/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)

/--
For $k \geq 2$, does the set $A$ contain only finitely many $k$-th powers?
-/
@[category research open, AMS 11]
theorem erdos_1108.k_th_powers : (∀ k ≥ 2,
    Set.Finite { a ∈ FactorialSums | ∃ m : ℕ, m ^ k = a }) ↔ answer(sorry) := by
  sorry

/--
Does the set $A$ contain only finitely many powerful numbers?
-/
@[category research open, AMS 11]
theorem erdos_1108.powerful_numbers :
    (Set.Finite { a ∈ FactorialSums | IsPowerful a }) ↔ answer(sorry) := by
  sorry

end Erdos1108
