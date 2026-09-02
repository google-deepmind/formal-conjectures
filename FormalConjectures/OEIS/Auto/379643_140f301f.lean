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

open Nat Finset

/--
A379643: List of $x$ coordinates of prime numbers in a Cartesian grid.
The sequence term $a(n)$ is given by the formula:
$$a(n) = \pi_{8,3}(p_n) - \pi_{8,7}(p_n)$$
where $\pi_{m,b}(x)$ is the number of primes $\le x$ which are congruent to $b \pmod m$
and $p_n$ is the $n$-th prime.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 3 : ℤ) - (count_primes_mod_b 7 : ℤ)


theorem a_one : a 1 = 0 := by
  inhabit Real
  norm_num[a]

theorem a_two : a 2 = 1 := by
  norm_num[a ]
  rfl

theorem a_three : a 3 = 1 := by
  delta a
  exact (5).nth_count Nat.prime_five▸rfl

theorem a_four : a 4 = 0 := by
  delta a
  push_cast +decide[show(3).nth _ = 7 from Nat.nth_count (by decide:(7).Prime)]

/--
A379731: List of $y$ coordinates of prime numbers in a Cartesian grid.
The sequence term $b(n)$ is given by the formula:
$$b(n) = \pi_{8,5}(p_n) - \pi_{8,1}(p_n)$$
where $p_n$ is the $n$-th prime.
-/
noncomputable def b (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 5 : ℤ) - (count_primes_mod_b 1 : ℤ)

/-- Conjecture: no prime appears on the negative y-axis.
That is, for every $n \ge 1$, if the $x$-coordinate $a(n)$ is $0$, then the $y$-coordinate $b(n)$ must be non-negative. -/
theorem oeis_379643_conjecture_0 : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by sorry
