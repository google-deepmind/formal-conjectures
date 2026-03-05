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

/-!
# Erdős Problem 291

*Reference:* [erdosproblems.com/291](https://www.erdosproblems.com/291)

Let $n \geq 1$ and define $L_n$ to be the least common multiple of $\{1, \ldots, n\}$ and $a_n$ by
$$\sum_{k=1}^{n} \frac{1}{k} = \frac{a_n}{L_n}.$$
Is it true that $\gcd(a_n, L_n) = 1$ and $\gcd(a_n, L_n) > 1$ both occur for infinitely
many $n$?

The second question is trivially yes (Steinerberger): any $n$ whose leading digit in
base 3 is 2 has $3 \mid \gcd(a_n, L_n)$.

The first question remains open.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset

namespace Erdos291

/-- The least common multiple of $\{1, \ldots, n\}$. -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- The numerator $a_n$ defined by $\sum_{k=1}^{n} \frac{1}{k} = \frac{a_n}{L_n}$, i.e.,
$a_n = \sum_{k=1}^{n} \frac{L_n}{k}$. Since $L_n$ is divisible by every $k \leq n$,
each summand is a natural number. -/
def harmonicLcmNumerator (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => lcmUpTo n / k

/--
Erdős Problem 291 [ErGr80, p.34]:

Both $\gcd(a_n, L_n) = 1$ and $\gcd(a_n, L_n) > 1$ occur for infinitely many $n \geq 1$,
where $L_n = \mathrm{lcm}(1, \ldots, n)$ and
$a_n = L_n \cdot H_n = \sum_{k=1}^{n} \frac{L_n}{k}$.
-/
@[category research open, AMS 11]
theorem erdos_291 : answer(sorry) ↔
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmUpTo n) = 1) ∧
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmUpTo n) > 1) := by
  sorry

/--
The second part of Erdős Problem 291: $\gcd(a_n, L_n) > 1$ occurs for infinitely many $n$.
This is trivially true (Steinerberger): any $n$ whose leading digit in base 3 is 2 has
$3 \mid \gcd(a_n, L_n)$.
-/
@[category research solved, AMS 11]
theorem erdos_291.variants.gcd_gt_one :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmUpTo n) > 1 := by
  sorry

end Erdos291
