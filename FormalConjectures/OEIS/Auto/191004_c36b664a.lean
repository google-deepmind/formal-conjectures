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

open Nat Int

/-- The condition that $p$ is an odd prime. -/
def is_odd_prime (p : ℕ) : Prop := p.Prime ∧ p ≠ 2

/--
A191004: Number of ways to write $n = p+q+(n \bmod 2)q$, where $p$ is an odd prime and $q \le n/2$ is a prime such that $\left(\frac{q}{n}\right)=1$ if $n$ is odd, and $\left(\frac{(q+1)/2}{n+1}\right)=1$ if $n$ is even.
-/
noncomputable def A191004 (n : ℕ) : ℕ :=
  let max_q := n / 2
  Finset.sum (Finset.range (max_q + 1)) fun q : ℕ =>
    if q.Prime ∧ 2 * q ≤ n then
      let p : ℕ := if n % 2 = 1 then n - 2 * q else n - q
      if p.Prime ∧ p ≠ 2 then -- p is an odd prime
        if n % 2 = 1 then
          -- Case n is odd: J(q, n) = 1
          if jacobiSym (q : ℤ) n = 1 then 1 else 0
        else
          -- Case n is even: J((q+1)/2, n+1) = 1
          if jacobiSym (((q + 1) / 2) : ℤ) (n + 1) = 1 then 1 else 0
      else 0
    else 0

theorem a_one : A191004 1 = 0 := by
  constructor

theorem a_two : A191004 2 = 0 := by
  trivial

theorem a_three : A191004 3 = 0 := by
  borelize ℂ
  aesop

theorem a_four : A191004 4 = 0 := by
  constructor

/-- Predicate for the odd case of Sun's refinement conjecture on A191004.
An odd number $m$ can be written as $p+2q$, where $p$ and $q$ are primes, and $\mathrm{JacobiSymbol}[q,p']=1$ for any prime divisor $p'$ of $m$. -/
def odd_refinement_exists (m : ℕ) : Prop :=
  ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ m = p + 2 * q ∧
    ∀ p' ∈ m.primeFactors, jacobiSym (q : ℤ) p' = 1

/-- Predicate for the even case of Sun's refinement conjecture on A191004.
An even number $m$ can be written as $p+q$, where $p$ and $q$ are primes and $q \le m/4$, and $\mathrm{JacobiSymbol}[(q+1)/2,p']=1$ for any prime divisor $p'$ of $m+1$. -/
def even_refinement_exists (m : ℕ) : Prop :=
  ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ m = p + q ∧ q ≤ m / 4 ∧
    ∀ p' ∈ (m + 1).primeFactors, jacobiSym (((q + 1) / 2) : ℤ) p' = 1

/-- Zhi-Wei Sun also conjectured the following refinement: Any odd number $2n+1>64$ not among $105, 247, 255, 1105$ can be written as $p+2q$, where $p$ and $q$ are primes, and $\mathrm{JacobiSymbol}[q,p']=1$ for any prime divisor $p'$ of $2n+1$; also, any even number $2n>8$ not among $32$ and $152$ can be written as $p+q$, where $p$ and $q \le n/2$ are primes, and $\mathrm{JacobiSymbol}[(q+1)/2,p']=1$ for any prime divisor $p'$ of $2n+1$. -/
theorem oeis_191004_sun_refinement_conjecture :
  (∀ m : ℕ, 64 < m ∧ Odd m ∧ m ∉ ({105, 247, 255, 1105} : Finset ℕ) → odd_refinement_exists m) ∧
  (∀ m : ℕ, 8 < m ∧ Even m ∧ m ∉ ({32, 152} : Finset ℕ) → even_refinement_exists m) := by
  sorry
