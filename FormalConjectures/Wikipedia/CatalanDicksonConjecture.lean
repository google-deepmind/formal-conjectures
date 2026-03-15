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

/-
# Catalan-Dickson Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan%E2%80%93Dickson_conjecture)
-/

namespace Catalan_Dickson

/-
Given k ∈ ℕ, the aliquot sequence is the sequence beginning with k
whose (n+1)st term is the sum of the proper divisors of its nth term.
-/
def aliquot (k : Nat) : Nat → Nat
  | 0 => k
  | n + 1 => (Nat.properDivisors (aliquot k n)).sum id

/-
A sociable number is a number whose aliquot sequence
is periodic with a period greater than or equal to 2.
Note that some definitions reserve the word sociable for numbers
whose aliquot sequence has a period of 3 or larger, and
call a number amicable when its period is exactly 2.
-/
def is_sociable (k : Nat) : Prop :=
  ∃ P : Nat,
  P ≥ 2 ∧ ∀ n : Nat, aliquot k n = aliquot k (n + P)

/-
The Catalan-Dickson Conjecture states that every aliquot sequence either:
reaches 1, reaches a perfect number, or reaches a sociable number.
-/
@[category research open, AMS 11 44]
theorem catalan_dickson_conjecture (k : Nat) :
    ∃ n : Nat,
    aliquot k n = 1 ∨
    (aliquot k n).Perfect ∨
    is_sociable (aliquot k n) := by
  sorry

end Catalan_Dickson
