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
# A001157

a(n) = sigma_2(n): sum of squares of divisors of n.

*References:*
- [A001157](https://oeis.org/A001157)
-/

namespace OeisA1157

/-- a n is the sum of squares of divisors of n. -/
def a (n : ℕ) : ℕ :=
  n.divisors.sum fun d => d ^ 2

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 5 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 10 := by rfl

@[category test, AMS 11]
lemma test_a_4 : a 4 = 21 := by rfl

@[category test, AMS 11]
lemma test_a_5 : a 5 = 26 := by rfl

open Nat Finset ArithmeticFunction

/--
Conjecture: For each k = 2,3,..., all the rational numbers sigma_k(n)/n^k = Sum_{d|n} 1/d^k (n = 1,2,3,...) have pairwise distinct fractional parts. - Zhi-Wei Sun, Oct 15 2015
-/
@[category research open, AMS 11]
theorem main_conjecture :
  ∀ k : ℕ, 2 ≤ k →
    ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ → n₁ ≠ n₂ →
      Int.fract (↑((sigma k) n₁) / (↑n₁ ^ k : ℚ)) ≠ Int.fract (↑((sigma k) n₂) / (↑n₂ ^ k : ℚ)) := by
  sorry

end OeisA1157
