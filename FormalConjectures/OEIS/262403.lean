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
# Additive decompositions of $\pi(T(n))$

Number of ways to write $\pi(T(n)) = \pi(T(k)) + \pi(T(m))$ with $1 < k < m < n$,
where $T(x) = \frac{x(x+1)}{2}$ is the $x$-th triangular number and $\pi(x)$ is the number of
primes not exceeding $x$.

*References:*
- [A262403](https://oeis.org/A262403)
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641)
  by *Zhi-Wei Sun*, arXiv:1402.6641 (2014)
-/

namespace OeisA262403

/-- The number of primes not exceeding the $x$-th triangular number $\frac{x(x+1)}{2}$. -/
def primeCountTriangular (x : ℕ) : ℕ :=
  Nat.primeCounting (x * (x + 1) / 2)

/--
Number of ways to write $\pi(T(n)) = \pi(T(k)) + \pi(T(m))$ with $1 < k < m < n$.
-/
def a (n : ℕ) : ℕ :=
  let target := primeCountTriangular n
  ∑ k ∈ Finset.Icc 2 (n - 2),
    ((Finset.Icc (k + 1) (n - 1)).filter (fun m =>
      target = primeCountTriangular k + primeCountTriangular m)).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- The set of exceptional integers $n > 4$ for which $a(n) = 1$. -/
def Singletons : Finset ℕ :=
  {5, 6, 7, 10, 12, 32, 38, 445, 727}

/--
Conjecture (i): $a(n) > 0$ for all $n > 4$, and $a(n) = 1$ only for
$n = 5, 6, 7, 10, 12, 32, 38, 445, 727$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 4 < n) :
    0 < a n ∧ (a n = 1 ↔ n ∈ Singletons) := by
  sorry

/--
Conjecture (ii), first assertion: All numbers $\pi(T(n))$ ($n = 1, 2, 3, \dots$) are pairwise
distinct.
-/
@[category research open, AMS 11]
theorem conjecture2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : primeCountTriangular m = primeCountTriangular n) : m = n := by
  sorry

/--
Conjecture (ii), second assertion: If $\sum_{i=j}^{k} \frac{1}{\pi(T(i))}$ and
$\sum_{r=s}^{t} \frac{1}{\pi(T(r))}$ with $1 < j \le k$ and $j \le s \le t$ have the same
fractional part but $(j, k) \ne (s, t)$, then $j = 2$, $k = 5$, and $s = t = 4$.
-/
@[category research open, AMS 11]
theorem conjecture3 (j k s t : ℕ) (hj : 1 < j) (hjk : j ≤ k) (hjs : j ≤ s)
    (hst : s ≤ t) (hne : (j, k) ≠ (s, t))
    (h : Int.fract (∑ i ∈ Finset.Icc j k, (primeCountTriangular i : ℚ)⁻¹) =
         Int.fract (∑ r ∈ Finset.Icc s t, (primeCountTriangular r : ℚ)⁻¹)) :
    j = 2 ∧ k = 5 ∧ s = 4 ∧ t = 4 := by
  sorry

end OeisA262403
