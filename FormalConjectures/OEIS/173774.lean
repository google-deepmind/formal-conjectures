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
# Arithmetic means of $(21k+8)\binom{2k}{k}^3$

The sequence is the arithmetic mean of $(21k+8)\binom{2k}{k}^3$ over $k = 0, \ldots, n-1$, for
$n \ge 1$.

*References:*
- [A173774](https://oeis.org/A173774), Zhi-Wei Sun, 2010.
- [A112029](https://oeis.org/A112029)
- [Su10] Zhi-Wei Sun, [A somewhat surprising conjecture](https://listserv.nodak.edu/cgi-bin/wa.exe?A2=NMBRTHRY;a39bf149.1002),
  message to the Number Theory List, 2010.
- [An10] Kasper Andersen, [Re: A somewhat surprising conjecture](http://listserv.nodak.edu/cgi-bin/wa.exe?A2=ind1002&L=nmbrthry&T=0&P=1395),
  message to the Number Theory List, 2010.
-/

@[expose] public section

namespace OeisA173774

/-- $a(n) = \frac{1}{n} \sum_{k=0}^{n-1} (21k+8)\binom{2k}{k}^3$, for $n \ge 1$. The sum is a
natural number and the division is in $\mathbb{Q}$. -/
def a (n : ℕ) : ℚ := ((∑ k ∈ Finset.range n, (21 * k + 8) * (2 * k).choose k ^ 3 : ℕ) : ℚ) / n

@[category test, AMS 5 11]
theorem a_1 : a 1 = 8 := by
  norm_num [a]

@[category test, AMS 5 11]
theorem a_2 : a 2 = 120 := by
  norm_num [a, Finset.sum_range_succ]

@[category test, AMS 5 11]
theorem a_3 : a 3 = 3680 := by
  norm_num [a, Finset.sum_range_succ, Nat.choose]

@[category test, AMS 5 11]
theorem a_4 : a 4 = 144760 := by
  norm_num [a, Finset.sum_range_succ, Nat.choose]

@[category test, AMS 5 11]
theorem a_5 : a 5 = 6427008 := by
  norm_num [a, Finset.sum_range_succ, Nat.choose]

/--
"On Feb 10 2010, Zhi-Wei Sun introduced the sequence and conjectured that each term a(n) is an
integer divisible by 4*binomial(2*n,n)."
- OEIS A173774.

Kasper Andersen confirmed this [An10]: $a(n) = 4\binom{2n}{n}\,b(n-1)$ with
$b(m) = \sum_{k=0}^{m} \binom{m+k}{k}^2$ (A112029). Formal proof by Wentao Li, with AI
assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000005"]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, a n = z ∧ 4 * ((2 * n).choose n : ℤ) ∣ z := by
  sorry

end OeisA173774
