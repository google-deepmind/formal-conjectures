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
# Least $m$ such that $\phi(m) = n!$

The smallest positive integer $m$ whose Euler totient equals $n!$.

*References:*
- [A055487](https://oeis.org/A055487)-/

namespace OeisA55487

/-- Least $m$ such that $\phi(m) = n!$. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ m.totient = n.factorial}

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨1, by decide⟩).csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨3, by decide⟩).csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by
  dsimp [a]
  change sInf {m | 0 < m ∧ m.totient = 6} = 7
  exact (Nat.isLeast_find ⟨7, by decide⟩).csInf_eq

@[category test, AMS 11]
theorem a_4 : a 4 = 35 := by
  dsimp [a]
  change sInf {m | 0 < m ∧ m.totient = 24} = 35
  exact (Nat.isLeast_find ⟨35, by decide⟩).csInf_eq

/-- Factorial primes: $n$ such that $n! + 1$ is prime (A002981). -/
def isFactorialPrime (n : ℕ) : Prop :=
  Nat.Prime (n.factorial + 1)

/-- The least prime $p > \sqrt{n!}$ such that $(p - 1) \mid n!$
    and $q = \frac{n!}{p - 1} + 1$ is prime. -/

noncomputable def p (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ Nat.sqrt n.factorial < p ∧ (p - 1) ∣ n.factorial ∧
    Nat.Prime (n.factorial / (p - 1) + 1)}

/-- The complementary prime factor $q = \frac{n!}{p - 1} + 1$. -/
noncomputable def q (n : ℕ) : ℕ :=
  n.factorial / (p n - 1) + 1

/--
Conjecture: unless $n! + 1$ is prime (i.e., $n \in \text{A002981}$), $a(n) = p q$ where $p$ is the
least prime $> \sqrt{n!}$ such that $(p - 1) \mid n!$ and $q = \frac{n!}{p - 1} + 1$ is prime.
- M. F. Hasler, Oct 04 2009

We assume $a(n) \ne 0$ and $(p(n)).\text{Prime}$ to ensure the `sInf` searches are non-empty
and do not collapse to $0 = 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) (h_not_prime : ¬ isFactorialPrime n)
    (ha : a n ≠ 0) (hp : (p n).Prime) :
    a n = p n * q n := by
  sorry

end OeisA55487
