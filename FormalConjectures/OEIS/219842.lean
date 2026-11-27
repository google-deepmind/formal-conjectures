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
module

public import FormalConjecturesUtil

/-!
# Writing $n = x + y$ with $2xy + 1$ prime

$a(n)$ is the number of ways to write $n = x + y$ with $0 < x \le y$ such that $2xy + 1$ is prime.

*References:*
- [A219842](https://oeis.org/A219842)
-/

@[expose] public section

namespace OeisA219842

open Filter

/-- The number of ways to write $n = x + y$ with $0 < x \le y$ and $2xy + 1$ prime.
Since $x \le y$ and $x + y = n$, the summand $x$ ranges over $1, \dots, \lfloor n/2 \rfloor$
and $y = n - x$. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter fun x => (2 * x * (n - x) + 1).Prime).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 3 := by decide

@[category test, AMS 11]
theorem a_9 : a 9 = 4 := by decide

@[category test, AMS 11]
theorem a_17 : a 17 = 1 := by decide

/--
$a(n) > 0$ for all $n > 1$, i.e. every integer $n > 1$ can be written as $x + y$ with
$0 < x \le y$ such that $2xy + 1$ is prime.
This has been verified for $n$ up to $10^8$.
- Zhi-Wei Sun, Nov 29 2012
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

/--
Every integer $n > 1$ can be written as $x + y$ with $0 < x \le y$ such that $2xy + 1$ is prime.
This is `conjecture` stated without the counting function `a`.
-/
@[category research open, AMS 11]
theorem conjecture.variants.exists (n : ℕ) (hn : 1 < n) :
    ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ (2 * x * y + 1).Prime := by
  sorry

/--
Every integer $n > 357$ can be written as $x + y$ with $x, y > 0$ such that $2xy - 1$ and
$2xy + 1$ are twin primes. This implies the twin prime conjecture.
- Zhi-Wei Sun, Nov 29 2012
-/
@[category research open, AMS 11]
theorem conjecture.variants.twin (n : ℕ) (hn : 357 < n) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (2 * x * y - 1).Prime ∧ (2 * x * y + 1).Prime := by
  sorry

/--
For each positive odd integer $m$, every sufficiently large integer $n$ can be written as $x + y$
with $x, y > 0$ such that $2xy + m$ and $2xy - m$ are both prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture.variants.general (m : ℕ) (hm : Odd m) :
    ∀ᶠ n in atTop, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (2 * x * y + m).Prime ∧ (2 * x * y - m).Prime := by
  sorry

end OeisA219842
