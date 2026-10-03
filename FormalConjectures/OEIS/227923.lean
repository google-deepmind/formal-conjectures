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
# Representations using Sophie Germain primes and twin prime pairs

Number of ways to write $n = x + y$ ($x, y > 0$) such that $6x - 1$ is a Sophie Germain prime
and $\{6y - 1, 6y + 1\}$ is a twin prime pair.

*References:*
- [A227923](https://oeis.org/A227923)
-/

namespace OeisA227923

/-- Number of ways to write $n = x + y$ ($x, y > 0$) such that $6x - 1$ is a Sophie Germain prime
and $\{6y - 1, 6y + 1\}$ is a twin prime pair. -/
def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).filter (fun x : ℕ =>
    let y := n - x
    (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime
  ) |>.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture (i), first part: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 1) : a n > 0 := by
  sorry

/--
Conjecture (i), second part: Any integer $n > 4$ not equal to $13$ can be written as $x + y$
with $x$ and $y$ distinct and greater than $1$ such that $6x - 1$ is a Sophie Germain prime
and $\{6y - 1, 6y + 1\}$ is a twin prime pair.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 4) (h13 : n ≠ 13) :
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  sorry

/--
Conjecture (ii), cousin prime variant: Any integer $n > 1$ can be written as $x + y$
($x, y > 0$) such that $6x - 1$ is a Sophie Germain prime and $\{6y + 1, 6y + 5\}$ is a
cousin prime pair.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : n > 1) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  sorry

/--
Conjecture (ii), sexy prime variant: Any integer $n > 1$ can be written as $x + y$
($x, y > 0$) such that $6x - 1$ is a Sophie Germain prime and $\{6y - 1, 6y + 5\}$ is a
sexy prime pair.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : n > 1) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y + 5).Prime := by
  sorry

end OeisA227923
