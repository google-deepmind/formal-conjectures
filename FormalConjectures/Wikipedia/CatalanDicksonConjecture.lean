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
# Catalan-Dickson Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan%E2%80%93Dickson_conjecture)
-/

namespace Catalan_Dickson

/--
Given k ∈ ℕ, the aliquot sequence is the sequence beginning with k
whose (n+1)st term is the sum of the proper divisors of its nth term.
-/
def aliquot (k : ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => ∑ i ∈ Nat.properDivisors (aliquot k n), i


-- Sanity checks for the aliquot sequence definition.

/-- 6 is a perfect number: its proper divisors {1, 2, 3} sum to 6, so it is a fixed point of
the aliquot map. -/
@[category test, AMS 11 44]
theorem catalan_dickson.test.aliquot_6_fixed : aliquot 6 1 = 6 := by native_decide

/-- 220 and 284 form an amicable pair: 220 → 284 → 220. -/
@[category test, AMS 11 44]
theorem catalan_dickson.test.amicable_220 : aliquot 220 2 = 220 := by native_decide

/-- The aliquot sequence from 12 reaches 1: 12 → 16 → 15 → 9 → 4 → 3 → 1. -/
@[category test, AMS 11 44]
theorem catalan_dickson.test.aliquot_12_reaches_1 : aliquot 12 6 = 1 := by native_decide

/--
A sociable number is a number whose aliquot sequence
is periodic with a period greater than or equal to 2.
Note that some definitions reserve the word sociable for numbers
whose aliquot sequence has a period of 3 or larger, and
call a number amicable when its period is exactly 2.
-/
def IsSociable (k : ℕ) : Prop :=
  ∃ P : Nat,
  P ≥ 2 ∧ ∀ n : ℕ, aliquot k n = aliquot k (n + P)

/--
The aliquot sequence starting at $k$ eventually reaches $1$, a perfect number,
or a sociable number.
-/
def AliquotTerminates (k : ℕ) : Prop :=
  ∃ n : ℕ, aliquot k n = 1 ∨ (aliquot k n).Perfect ∨ IsSociable (aliquot k n)

/-
The Catalan-Dickson Conjecture states that every aliquot sequence either:
reaches $1$, reaches a perfect number, or reaches a sociable number.
-/
@[category research open, AMS 11 44]
theorem catalan_dickson_conjecture (k : ℕ) : AliquotTerminates k := by
  sorry

/-- 276 is the smallest number whose aliquot sequence has not been determined (Lehmer five). -/
@[category research open, AMS 11 44]
theorem catalan_dickson.variants.lehmer_276 : AliquotTerminates 276 := by sorry

/-- 552 is the second of the Lehmer five whose aliquot sequence has not been determined. -/
@[category research open, AMS 11 44]
theorem catalan_dickson.variants.lehmer_552 : AliquotTerminates 552 := by sorry

/-- 564 is the third of the Lehmer five whose aliquot sequence has not been determined. -/
@[category research open, AMS 11 44]
theorem catalan_dickson.variants.lehmer_564 : AliquotTerminates 564 := by sorry

/-- 660 is the fourth of the Lehmer five whose aliquot sequence has not been determined. -/
@[category research open, AMS 11 44]
theorem catalan_dickson.variants.lehmer_660 : AliquotTerminates 660 := by sorry

/-- 966 is the fifth of the Lehmer five whose aliquot sequence has not been determined. -/
@[category research open, AMS 11 44]
theorem catalan_dickson.variants.lehmer_966 : AliquotTerminates 966 := by sorry

end Catalan_Dickson
