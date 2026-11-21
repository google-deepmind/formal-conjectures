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
module

public import FormalConjecturesUtil

/-!
# Sums of a prime with prime index and a semiprime

OEIS A282355 counts representations of an integer as a sum of a prime whose one-based prime
index is itself prime and a semiprime. A semiprime may be the square of a prime.

*References:*
- [A282355](https://oeis.org/A282355)
- [A006450](https://oeis.org/A006450)
- [A001358](https://oeis.org/A001358)
-/

@[expose] public section

namespace OeisA282355

/-- A prime whose position in the increasing list of primes is prime. -/
def IsSuperprime (p : ℕ) : Prop := p.Prime ∧ (Nat.primeCounting p).Prime

instance (p : ℕ) : Decidable (IsSuperprime p) := inferInstanceAs
  (Decidable (p.Prime ∧ (Nat.primeCounting p).Prime))

/-- The number of superprime summands $p \le n$ for which $n-p$ is semiprime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p => IsSuperprime p ∧ Nat.IsSemiprime (n - p)).card

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_7 : a 7 = 1 := by decide +kernel

@[category test, AMS 11]
theorem a_9 : a 9 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_11 : a 11 = 1 := by decide +kernel

/-- The last integer excluded by the strict conjectured bound has no representation. -/
@[category test, AMS 11]
theorem a_527 : a 527 = 0 := by decide +kernel

@[category test, AMS 11]
theorem a_528 : a 528 = 8 := by decide +kernel

@[category test, AMS 11]
theorem not_superprime_two : ¬ IsSuperprime 2 := by decide +kernel

@[category test, AMS 11]
theorem superprime_three : IsSuperprime 3 := by decide +kernel

@[category test, AMS 11]
theorem not_semiprime_zero : ¬ Nat.IsSemiprime 0 := by decide +kernel

@[category test, AMS 11]
theorem not_semiprime_one : ¬ Nat.IsSemiprime 1 := by decide +kernel

@[category test, AMS 11]
theorem not_semiprime_two : ¬ Nat.IsSemiprime 2 := by decide +kernel

@[category test, AMS 11]
theorem semiprime_four : Nat.IsSemiprime 4 := by decide +kernel

/-- Representations are counted by the superprime summand, not by ordered prime factorizations. -/
@[category test, AMS 11]
theorem summands_at_nine :
    ((Finset.range 10).filter fun p => IsSuperprime p ∧ Nat.IsSemiprime (9 - p)) = {3, 5} := by
  decide +kernel

/-- "Conjecture: $a(n) > 0$ for all $n > 527$" -/
@[category research open, AMS 11]
theorem superprime_semiprime_representations : ∀ n : ℕ, 527 < n → 0 < a n := by
  sorry

end OeisA282355
