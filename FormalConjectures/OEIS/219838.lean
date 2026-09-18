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
# Partitions of $n$ into $x + y$ with $(xy)^2 + xy + 1$ prime

Number of ways to write $n$ as $x + y$ with $0 < x \le y$ and $(xy)^2 + xy + 1$ prime.

*References:*
- [A219838](https://oeis.org/A219838)
-/

namespace OeisA219838

/-- Number of ways to write $n$ as $x + y$ with $0 < x \le y$ and $(xy)^2 + xy + 1$ prime. -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).filter (fun x : ℕ =>
    let xy := x * (n - x)
    Nat.Prime (xy ^ 2 + xy + 1)
  ) |>.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 2 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 1) : a n > 0 := by
  sorry

/--
The author also guesses that any integer $n > 1157$ can be written as $x + y$ with $x$ and $y$
positive integers, and $(xy)^2 + xy + 1$ and $(xy)^2 + xy - 1$ twin primes.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 1157) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime ((x * y) ^ 2 + x * y - 1) ∧ Nat.Prime ((x * y) ^ 2 + x * y + 1) := by
  sorry

/--
Conjecture: For each prime $p$, any sufficiently
large integer $n$ can be written as $x + y$, where $x$ and $y$ are positive integers with
$\frac{(xy)^p - 1}{xy - 1}$ prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : p.Prime) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
        Nat.Prime (((x * y) ^ p - 1) / (x * y - 1)) := by
  sorry

end OeisA219838
