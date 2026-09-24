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
# Representations of $n$ as $x^2 + \phi(y^2) + \phi(z^2)$

Number of ordered ways to write $n$ as $x^2 + \phi(y^2) + \phi(z^2)$ ($x \ge 0$ and $0 < y \le z$)
with $y$ or $z$ prime, where $\phi(\cdot)$ is Euler's totient function.

*References:*
- [A262781](https://oeis.org/A262781)
-/

namespace OeisA262781

/--
Number of ordered ways to write $n$ as $x^2 + \phi(y^2) + \phi(z^2)$ ($x \ge 0$ and $0 < y \le z$)
with $y$ or $z$ prime.
-/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (n + 1),
    ∑ y ∈ Finset.Ico 1 (n + 1),
      ∑ z ∈ Finset.Ico y (n + 1),
        if (y.Prime ∨ z.Prime) ∧ x ^ 2 + Nat.totient (y ^ 2) + Nat.totient (z ^ 2) = n then
          1
        else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- The set of exceptional values of $n$ for which $a(n) = 1$. -/
def Singletons : Finset ℕ :=
  {3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649}

/--
Conjecture (i): $a(n) > 0$ for all $n > 6$, and $a(n) = 1$ only for
$n = 3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) :
    (6 < n → 0 < a n) ∧ (a n = 1 ↔ n ∈ Singletons) := by
  sorry

/--
Conjecture (ii): For any integer $n > 4$, we can write $2n$ as $\phi(p^2) + \phi(x^2) + \phi(y^2)$
with $p$ prime and $p \le x \le y$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 4 < n) :
    ∃ p x y : ℕ, p.Prime ∧ p ≤ x ∧ x ≤ y ∧
      2 * n = Nat.totient (p ^ 2) + Nat.totient (x ^ 2) + Nat.totient (y ^ 2) := by
  sorry

end OeisA262781
