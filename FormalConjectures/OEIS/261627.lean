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
# Primes $p$ such that $n - (p n' - 1)$ and $n + (p n' - 1)$ are both prime

Number of primes $p$ such that $n - (p n' - 1)$ and $n + (p n' - 1)$ are both prime,
where $n'$ is $1$ or $2$ according as $n$ is odd or even.

*References:*
- [A261627](https://oeis.org/A261627)
- [Conjectures involving primes and quadratic forms](https://arxiv.org/abs/1211.1588)
  by *Zhi-Wei Sun*, arXiv:1211.1588 (2012-2015)
-/

namespace OeisA261627

/--
The number of primes $p$ such that $n - (p n' - 1)$ and $n + (p n' - 1)$ are both prime,
where $n' = 1$ if $n$ is odd and $n' = 2$ if $n$ is even.
-/
def a (n : ℕ) : ℕ :=
  let n' : ℕ := if n % 2 = 1 then 1 else 2
  ((Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧
    let k := p * n' - 1
    k < n ∧ Nat.Prime (n - k) ∧ Nat.Prime (n + k))).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- The set of exceptional values of $n$ for which $a(n) = 1$. -/
def Singletons : Finset ℕ :=
  {5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142}

/--
Conjecture: $a(n) > 0$ for all $n > 6$, and $a(n) = 1$ only for
$n = 5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) :
    (6 < n → 0 < a n) ∧ (a n = 1 ↔ n ∈ Singletons) := by
  sorry

end OeisA261627
