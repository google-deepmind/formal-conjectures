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
# Sequence $\frac{(8n)! n!}{(4n)! (3n)! (2n)!}$

The sequence $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$, which is always an integer for $n \ge 0$.

*References:*
- [A211420](https://oeis.org/A211420)
- [OEIS Open](https://arxiv.org/abs/2608.11941)
  by *Tom Adamczewski*, arXiv:2608.11941 (2026)
- [OEIS-A211420](https://github.com/anshM123/OEIS-A211420)
  by *Ansh Mishra* and *Aryan Senthilkumar* (2026)
-/

namespace OeisA211420

/-- $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$. -/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/-- The product $\prod_{i=0}^r (8n - (2i + 1))$ in $\mathbb{Z}$. -/
def oddDescendingProduct (n r : ℕ) : ℤ :=
  ∏ i ∈ Finset.range (r + 1), ((8 * n : ℤ) - (2 * i + 1 : ℤ))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 140 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 60060 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 29745716 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 15628090140 := by decide

/--
"It appears that $35 \cdot a(n)/(n + 1)$, $3 \cdot a(n)/(2n + 1)$ and $5 \cdot a(n)/(3n + 1)$ are
integers for all $n$."
- _Peter Bala_, Aug 26 2025

The divisibility $(3n + 1) \mid 5 a(n)$ follows from a result of Z.-W. Sun (2012). The full
statement was proved and formalized in Lean 4 by Ansh Mishra and Aryan Senthilkumar (with Claude).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/anshM123/OEIS-A211420/blob/2bd4dbf1185a9fa8edc2cb9a61d471583d018d08/lean/DMSolutions/OEIS_A211420/Solution.lean#L25-L28"]
theorem conjecture1 (n : ℕ) :
    (n + 1) ∣ 35 * a n ∧ (2 * n + 1) ∣ 3 * a n ∧ (3 * n + 1) ∣ 5 * a n := by
  sorry

/--
"More generally, we conjecture that there are constants $C(k, r) > 0$, $k = 1, 2$ or $3$, $r \ge 1$,
such that $a(n) \cdot C(k, r)/((kn + 1)(kn + 2)\cdots(kn + r))$ is an integer for all $n$."
- _Peter Bala_, Aug 26 2025

Proved and formalized in Lean 4 by DannyExperiments (2026) and independently by Ansh Mishra and
Aryan Senthilkumar (with Claude).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/anshM123/OEIS-A211420/blob/2bd4dbf1185a9fa8edc2cb9a61d471583d018d08/lean/DMSolutions/OEIS_A211420/Solution.lean#L30-L33"]
theorem conjecture2 (k r : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, (k * n + 1).ascFactorial r ∣ C * a n := by
  sorry

/--
"It also appears that $a(n)$ is divisible by $8n - 1$ for all $n$."
- _Peter Bala_, Aug 26 2025

Proved and formalized in Lean 4 by Ansh Mishra and Aryan Senthilkumar (with Claude).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/anshM123/OEIS-A211420/blob/2bd4dbf1185a9fa8edc2cb9a61d471583d018d08/lean/DMSolutions/OEIS_A211420/Solution.lean#L35-L38"]
theorem conjecture3 (n : ℕ) :
    ((8 * n : ℤ) - 1) ∣ (a n : ℤ) := by
  sorry

/--
"More generally, we conjecture that there are constants $K(r) > 0$, $r \ge 0$, such that
$a(n) \cdot K(r)/((8n - 1)(8n - 3)\cdots(8n - (2r+1)))$ is an integer for all $n$."
- _Peter Bala_, Aug 26 2025

Proved by Adamczewski (2026), and also by Ansh Mishra and Aryan Senthilkumar
(with Claude).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/anshM123/OEIS-A211420/blob/2bd4dbf1185a9fa8edc2cb9a61d471583d018d08/lean/DMSolutions/OEIS_A211420/Solution.lean#L40-L43"]
theorem conjecture4 (r : ℕ) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, oddDescendingProduct n r ∣ (a n : ℤ) * K := by
  sorry

end OeisA211420
