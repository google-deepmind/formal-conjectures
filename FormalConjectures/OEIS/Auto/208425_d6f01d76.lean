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

open Nat BigOperators Finset

/--
A208425: Expansion of $\sum_{n\ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$.
The $n$-th term $a(n)$ is given by the known combinatorial identity:
$$ a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k} $$
-/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) * ((n - k).choose k) * ((n + k).choose k)


theorem a_zero : a 0 = 1 := by
  trivial

theorem a_one : a 1 = 1 := by
  constructor

theorem a_two : a 2 = 7 := by
  constructor

theorem a_three : a 3 = 25 := by
  rfl


/-- Conjecture: (i) For any prime p > 3 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
theorem oeis_208425_conjecture_0 (p : ℕ) (hp : p.Prime) (hpgt3 : p > 3) (n : ℕ) (hn : n > 0) :
  padicValRat p (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) ≥ 0 :=
by sorry
