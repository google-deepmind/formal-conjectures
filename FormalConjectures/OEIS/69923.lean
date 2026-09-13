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
# Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$

The sequence $a(n)$ counts the number of primes $p$ in the interval $[2^n, 2^n + p_n]$,
where $p_n$ is the $n$-th prime ($p_1 = 2, p_2 = 3, \dots$):
$$a(n) = |\{p \text{ prime} \mid 2^n \le p \le 2^n + p_n\}|$$
for $n \ge 1$, and $a(0) = 0$.

*References:*
- [A069923](https://oeis.org/A069923)-/

namespace OeisA69923

open Finset

/-- Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p := Nat.nth Nat.Prime (n - 1)
    ((Icc (2 ^ n) (2 ^ n + p)).filter Nat.Prime).card

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  change ((Icc (2 ^ 1) (2 ^ 1 + Nat.nth Nat.Prime 0)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_zero_eq_two]
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  change ((Icc (2 ^ 2) (2 ^ 2 + Nat.nth Nat.Prime 1)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_one_eq_three]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  change ((Icc (2 ^ 3) (2 ^ 3 + Nat.nth Nat.Prime 2)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_two_eq_five]
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  change ((Icc (2 ^ 4) (2 ^ 4 + Nat.nth Nat.Prime 3)).filter Nat.Prime).card = 3
  rw [Nat.nth_prime_three_eq_seven]
  decide

/--
For any $n > 0$, is there always at least one prime $p$ such that
$2^n \le p \le 2^n + \mathrm{prime}(n)$?
(checked up to $n = 250$). In this case, that would be stronger than the Schinzel conjecture:
"for $m > 1$ there's at least one prime $p$ such that $m \le p \le m + \log(m)^2$" since,
for $n > 2$, $\mathrm{prime}(n) < \log(2^n)^2 = n^2 \log(2)$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : 1 ≤ a n := by
  sorry

end OeisA69923
