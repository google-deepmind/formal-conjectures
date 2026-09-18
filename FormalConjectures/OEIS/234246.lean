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
# Number of integers $0 < k < n$ such that $k \phi(n - k) + 1$ is a square

*References:*
- [A234246](https://oeis.org/A234246)
-/

namespace OeisA234246

open ArithmeticFunction

/--
The primary defining sequence `a`.
$a(n)$ is the number of integers $0 < k < n$ such that $k \phi(n - k) + 1$ is a square,
where $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    let m := k * (n - k).totient + 1
    if ∃ r ≤ m, r * r = m then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide

/--
Conjecture (i): $a(n) > 0$ if $n$ is not a divisor of $6$.
The only values of $n$ with $a(n) = 1$ are $4, 5, 8, 9, 12, 13, 24, 33, 49$.
-/
@[category research open, AMS 11]
theorem conjecture1 :
    (∀ n : ℕ, 0 < n → ¬(n ∣ 6) → 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔ n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ)) := by
  sorry

/--
Conjecture (ii): If $n \ge 60$, then $k + \phi(n - k)$ is a square for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 60 ≤ n) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k + (n - k).totient) := by
  sorry

/--
Conjecture (ii): If $n > 60$, then $\sigma(k) + \phi(n - k)$ is a square for some $0 < k < n$,
where $\sigma(k)$ is the sum of all positive divisors of $k$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 60 < n) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (sigma 1 k + (n - k).totient) := by
  sorry

/--
Conjecture (iii): If $n > 7$ is not equal to $10$ or $20$, then $\phi(k)\phi(n - k) + 1$
is a square for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 7 < n) (hne10 : n ≠ 10) (hne20 : n ≠ 20) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k.totient * (n - k).totient + 1) := by
  sorry

/--
Conjecture (iv): If $n > 7$ is not equal to $10$ or $19$, then $(\phi(k) + \phi(n - k)) / 2$
is a triangular number for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture5 (n : ℕ) (hn : 7 < n) (hne10 : n ≠ 10) (hne19 : n ≠ 19) :
    ∃ k, 0 < k ∧ k < n ∧ ∃ m : ℕ, (k.totient + (n - k).totient) / 2 = m * (m + 1) / 2 := by
  sorry

end OeisA234246
