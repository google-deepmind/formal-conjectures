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
# Lerch quotients of odd primes

The Lerch quotient of an odd prime $p$ is given by
$$L_p = \frac{\left(\sum_{k=1}^{p-1} q_p(k)\right) - w_p}{p}$$
where $q_p(k) = (k^{p-1}-1)/p$ is the Fermat quotient and $w_p = ((p-1)!+1)/p$ is the Wilson
quotient. For $n > 1$, $a(n)$ is the Lerch quotient of the $n$-th prime $p_n$.

*References:*
- [A197630](https://oeis.org/A197630)
-/

namespace OeisA197630

/-- The Fermat quotient $q_p(k) = (k^{p-1}-1)/p$. -/
def fermatQuotient (k p : ℕ) : ℤ :=
  ((k : ℤ) ^ (p - 1) - 1) / (p : ℤ)

/-- The Wilson quotient $w_p = ((p-1)!+1)/p$. -/
def wilsonQuotient (p : ℕ) : ℤ :=
  ((p - 1).factorial + 1 : ℤ) / (p : ℤ)

/-- The Lerch quotient of $p$:
$\frac{(\sum_{k=1}^{p-1} q_p(k)) - w_p}{p}$. -/
def lerchQuotient (p : ℕ) : ℕ :=
  let sumQ : ℤ := ∑ k ∈ Finset.Ico 1 p, fermatQuotient k p
  ((sumQ - wilsonQuotient p) / (p : ℤ)).natAbs

/-- Lerch quotients of odd primes: $a(n)$ is the Lerch quotient of the $n$-th prime $p_n$ for
$n > 1$, and $0$ for $n \le 1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if 1 < n then
    lerchQuotient (Nat.nth Nat.Prime (n - 1))
  else
    0

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  have h : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  simp only [a, show (2 - 1 : ℕ) = 1 by rfl, h]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 13 := by
  have h : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  simp only [a, show (3 - 1 : ℕ) = 2 by rfl, h]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1356 := by
  have h : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  simp only [a, show (4 - 1 : ℕ) = 3 by rfl, h]
  decide

/--
"Is $13$ the only Lerch quotient that is itself prime?"
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) (hp : (a n).Prime) : a n = 13 := by
  sorry

end OeisA197630
