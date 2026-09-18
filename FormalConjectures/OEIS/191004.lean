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
# Representations of $n = p + q + (n \bmod 2)q$ with Jacobi symbol constraints

The sequence $a(n)$ counts the number of ways to write $n = p + q + (n \bmod 2)q$, where $p$ is an
odd prime and $q \le n/2$ is a prime such that $\left(\frac{q}{n}\right) = 1$ if $n$ is odd, and
$\left(\frac{(q+1)/2}{n+1}\right) = 1$ if $n$ is even.

*References:*
- [A191004](https://oeis.org/A191004)
- [Conjectures involving primes and quadratic forms](https://arxiv.org/abs/1211.1588)
  by *Zhi-Wei Sun*, arXiv:1211.1588 (2012)
-/

namespace OeisA191004

/--
Number of ways to write $n = p + q + (n \bmod 2)q$, where $p$ is an odd prime and $q \le n/2$ is a
prime such that $\left(\frac{q}{n}\right) = 1$ if $n$ is odd, and
$\left(\frac{(q+1)/2}{n+1}\right) = 1$ if $n$ is even.
-/
def a (n : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (n / 2 + 1),
    if q.Prime ∧ 2 * q ≤ n then
      let p := if n % 2 = 1 then n - 2 * q else n - q
      if p.Prime ∧ p ≠ 2 then
        if n % 2 = 1 then
          if jacobiSym (q : ℤ) n = 1 then 1 else 0
        else
          if jacobiSym (((q + 1) / 2) : ℤ) (n + 1) = 1 then 1 else 0
      else 0
    else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by decide

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by decide +native

/-- Value of the sequence `a` at 14. -/
@[category test, AMS 11]
theorem a_14 : a 14 = 2 := by decide +native

/--
Conjecture: $a(n) > 0$ for all $n > 5$.
- _Zhi-Wei Sun_, Dec 30 2012
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 5 < n) : 0 < a n := by
  sorry

/--
Refinement conjecture (odd case): Any odd number $2n+1 > 64$ not among $105, 247, 255, 1105$ can be
written as $p + 2q$, where $p$ and $q$ are primes, and $\left(\frac{q}{p'}\right) = 1$ for any prime
divisor $p'$ of $2n+1$.
- _Zhi-Wei Sun_, Dec 30 2012
-/
@[category research open, AMS 11]
theorem conjecture2 (m : ℕ) (hm : 64 < m) (hodd : Odd m)
    (hnot : m ∉ ({105, 247, 255, 1105} : Finset ℕ)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 2 * q ∧
      ∀ p' ∈ m.primeFactors, jacobiSym (q : ℤ) p' = 1 := by
  sorry

/--
Refinement conjecture (even case): Any even number $2n > 8$ not among $32$ and $152$ can be written
as $p + q$, where $p$ and $q \le n/2$ are primes, and $\left(\frac{(q+1)/2}{p'}\right) = 1$ for any
prime divisor $p'$ of $2n+1$.
- _Zhi-Wei Sun_, Dec 30 2012
-/
@[category research open, AMS 11]
theorem conjecture3 (m : ℕ) (hm : 8 < m) (heven : Even m)
    (hnot : m ∉ ({32, 152} : Finset ℕ)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + q ∧ q ≤ m / 4 ∧
      ∀ p' ∈ (m + 1).primeFactors, jacobiSym (((q + 1) / 2) : ℤ) p' = 1 := by
  sorry

end OeisA191004
