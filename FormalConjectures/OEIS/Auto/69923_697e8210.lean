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

open Nat

/--
A069923: Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, $p_n$, starting with $p_1 = 2$.
The $n$-th prime for $n \ge 1$ is $\mathrm{Nat.nth} \, \mathrm{Nat.Prime} \, (n-1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let L := 2^n
    let U := L + p_n
    -- The number of primes $p$ in $[L, U]$ is $\pi(U) - \pi(L-1)$.
    primeCounting U - primeCounting (L - 1)


theorem a_one : a 1 = 2 := by
  rcases(Algebra.id.smul_eq_mul 10 1).dvd
  norm_num+decide[a]

theorem a_two : a 2 = 2 := by
  delta a
  norm_num+decide[Nat.primeCounting]

theorem a_three : a 3 = 2 := by
  delta and a
  simp_all+decide[show(2).nth _ = 5 from Nat.nth_count (by decide:Nat.prime_five),Nat.primeCounting]

theorem a_four : a 4 = 3 := by
  delta a
  norm_num+decide[show(3).nth _ = 7 from Nat.nth_count (by decide:(7).Prime),Nat.primeCounting]


/--
Conjecture A069923: For any n > 0, there is always at least one prime p such that
$2^n \le p \le 2^n + \mathrm{prime}(n)$.
Equivalently, $a(n) \ge 1$ for all $n \ge 1$.
(checked up to n=250)
-/
theorem oeis_A069923_conjecture (n : ℕ) (hn : 0 < n) :
  1 ≤ a n :=
by sorry
