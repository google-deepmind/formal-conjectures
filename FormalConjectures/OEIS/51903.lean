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
# Maximum exponent in the prime factorization of $n$

*References:*
- [A051903](https://oeis.org/A051903)-/

namespace OeisA51903

/-- Maximum exponent in the prime factorization of $n$. -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide +native

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  decide +native

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide +native

/--
Are there composite numbers $n > 4$ such that $n \equiv a(n) \pmod{\phi(n)}$?
- Thomas Ordowski, Dec 02 2019
-/
@[category research open, AMS 11]
theorem conjecture1 :
    answer(sorry) ↔ ∃ n : ℕ, 4 < n ∧ ¬ n.Prime ∧ n.totient ∣ (n - a n) := by
  sorry

/--
Are there odd numbers $n$ such that $a(n) > 1$ and $n \equiv a(n) \pmod{\lambda(n)}$?
(Equivalently, odd numbers $n$ such that $a(n) > 1$ and $b^n \equiv b^{a(n)} \pmod n$ for all $b$.)
- Thomas Ordowski, Dec 02 2019
-/
@[category research open, AMS 11]
theorem conjecture2 :
    answer(sorry) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  sorry

/--
Are there odd numbers $n$ such that $a(n) > 1$ and $n \equiv a(n) \pmod{\operatorname{ord}_n(2)}$?
(Equivalently, odd numbers $n$ such that $a(n) > 1$ and $2^n \equiv 2^{a(n)} \pmod n$.)
- Thomas Ordowski, Dec 02 2019
-/
@[category research open, AMS 11]
theorem conjecture3 :
    answer(sorry) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  sorry

end OeisA51903

