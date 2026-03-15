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

The second question is yes (Steinerberger): any $n$ whose leading digit in
base 3 is 2 has $3 \mid \gcd(a_n, L_n)$.

The first question remains open.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Sh16] Shiu, P., _The denominators of harmonic numbers_. arXiv:1607.02863 (2016).

[WuYa22] Wu, B.-L. and Yan, X.-H., _On the denominators of harmonic numbers. IV_.
C. R. Math. Acad. Sci. Paris (2022), 53–57.

See also OEIS sequence [A110566](https://oeis.org/A110566).
-/

open Finset

namespace Erdos291

/-- The numerator $a_n$ defined by $\sum_{k=1}^{n} \frac{1}{k} = \frac{a_n}{L_n}$, i.e.,
$a_n = \sum_{k=1}^{n} \frac{L_n}{k}$, where $L_n = \mathrm{lcm}(1, \ldots, n)$.
Since $L_n$ is divisible by every $k \leq n$, each summand is a natural number. -/
def harmonicLcmNumerator (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => lcmInterval 0 n / k

/--
Erdős Problem 291 [ErGr80, p.34]:

Both $\gcd(a_n, L_n) = 1$ and $\gcd(a_n, L_n) > 1$ occur for infinitely many $n \geq 1$,
where $L_n = \mathrm{lcm}(1, \ldots, n)$ and
$a_n = L_n \cdot H_n = \sum_{k=1}^{n} \frac{L_n}{k}$.
-/
@[category research open, AMS 11]
theorem erdos_291 : answer(sorry) ↔
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmInterval 0 n) = 1) ∧
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmInterval 0 n) > 1) := by
  sorry

/--
The first part of Erdős Problem 291: $\gcd(a_n, L_n) = 1$ occurs for infinitely many $n$.
This remains open. Shiu [Sh16] predicts approximately $x / \log x$ coprime cases in $[1, x]$.
-/
@[category research open, AMS 11]
theorem erdos_291.variants.gcd_eq_one :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmInterval 0 n) = 1 := by
  sorry

/--
The second part of Erdős Problem 291: $\gcd(a_n, L_n) > 1$ occurs for infinitely many $n$.
This is true (Steinerberger): any $n$ whose leading digit in base 3 is 2 has
$3 \mid \gcd(a_n, L_n)$.
-/
@[category research solved, AMS 11]
theorem erdos_291.variants.gcd_gt_one :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmInterval 0 n) > 1 := by
  sorry

end Erdos291
