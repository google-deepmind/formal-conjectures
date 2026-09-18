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
# Expansion of $\sum_{n \ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$

The sequence $a(n)$ given by the expansion of
$\sum_{n \ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$, which satisfies
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k}.$$

*References:*
- [A208425](https://oeis.org/A208425)
-/

namespace OeisA208425

/-- Expansion of $\sum_{n \ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$, given by
$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).choose k * (n + k).choose k

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 7 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 25 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 151 := by decide

/--
"Conjecture: (i) For any prime $p > 3$ and positive integer $n$, the number
$(a(pn)-a(n))/(pn)^3$ is always a $p$-adic integer."
- _Zhi-Wei Sun_, Nov 12 2016
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hpgt3 : 3 < p) (n : ℕ) (hn : 0 < n) :
    0 ≤ padicValRat p (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) := by
  sorry

/--
"For any prime $p \equiv 1 \pmod{3}$, we have
$\sum_{k=0}^{p-1} a(k) \equiv \binom{2(p-1)/3}{(p-1)/3} \pmod{p^2}$."
- _Zhi-Wei Sun_, Nov 12 2016
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    (∑ k ∈ Finset.range p, a k) % (p ^ 2) =
      ((2 * (p - 1) / 3).choose ((p - 1) / 3)) % (p ^ 2) := by
  sorry

/--
"For any prime $p \equiv 2 \pmod{3}$, we have
$\sum_{k=0}^{p-1} a(k) \equiv \frac{2p}{\binom{2(p+1)/3}{(p+1)/3}} \pmod{p^2}$."
- _Zhi-Wei Sun_, Nov 12 2016
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 2) :
    ((∑ k ∈ Finset.range p, (a k : ℚ)) -
      (2 * p : ℚ) / ((2 * (p + 1) / 3).choose ((p + 1) / 3) : ℚ)).num % (p ^ 2 : ℤ) = 0 := by
  sorry

end OeisA208425
