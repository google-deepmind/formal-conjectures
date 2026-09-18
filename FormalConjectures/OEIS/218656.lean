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
# Partitions $2n + 1 = x + y$ with $x^4 + y^4$ prime

For $n \ge 1$, $a(n)$ is the number of ways to write $2n + 1$ as $x + y$ with $0 < x < y$ such that
$x^4 + y^4$ is prime.

*References:*
- [A218656](https://oeis.org/A218656)
-/

namespace OeisA218656

/-- `a n` is the number of ways to write $2n + 1$ as $x + y$ with $0 < x < y$ and
$x^4 + y^4$ prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 n,
    if Nat.Prime (x ^ 4 + (2 * n + 1 - x) ^ 4) then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by native_decide

/--
Conjecture: $a(n) > 0$ for all $n \ge 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  sorry

/--
Conjecture: If $x^4 + y^4$ in the definition of $a(n)$ is
replaced by $x^2 + y^2$, then the count is positive for all $n \ge 1$.
- _Thomas Ordowski_, Nov 03 2012
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ Nat.Prime (x ^ 2 + (2 * n + 1 - x) ^ 2) := by
  sorry

/--
Conjecture: If $x^4 + y^4$ in the definition of $a(n)$ is replaced by $x^8 + y^8$, then the count
is positive for all $n \ge 1$ except for $2n + 1 \in \{7, 9, 55, 73, 75, 105\}$
(i.e., $n \in \{3, 4, 27, 36, 37, 52\}$).
- _Thomas Ordowski_, Nov 03 2012; exceptions noted by _Mauro Fiorentini_, Sep 22 2023
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1 ≤ n) (h_exc : n ∉ ({3, 4, 27, 36, 37, 52} : Set ℕ)) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ Nat.Prime (x ^ 8 + (2 * n + 1 - x) ^ 8) := by
  sorry

/--
Conjecture: If $x^4 + y^4$ in the definition of $a(n)$ is replaced by $x^{16} + y^{16}$, then the
count is positive for all $n \ge 1$ except for $2n + 1 \in \{5, 9\}$ (i.e., $n \in \{2, 4\}$).
- _Thomas Ordowski_, Nov 03 2012; exceptions noted by _Mauro Fiorentini_, Sep 22 2023
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 1 ≤ n) (h_exc : n ∉ ({2, 4} : Set ℕ)) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ Nat.Prime (x ^ 16 + (2 * n + 1 - x) ^ 16) := by
  sorry

end OeisA218656
