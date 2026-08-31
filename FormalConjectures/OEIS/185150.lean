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
# Number of odd primes between $n^2$ and $(n+1)^2$ with $(n/p) = 1$

$a(n)$ is the number of odd primes $p$ between $n^2$ and $(n+1)^2$ such that the Legendre symbol
$\left(\frac{n}{p}\right) = 1$.

*References:*
- [A185150](https://oeis.org/A185150)
- Z.-W. Sun, "Conjectures involving primes and quadratic forms", arXiv preprint
  [arXiv:1211.1588](https://arxiv.org/abs/1211.1588) [math.NT], 2012.-/

namespace OeisA185150

/-- Number of odd primes $p \in (n^2, (n+1)^2)$ with $(n/p) = 1$. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2),
    if p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1 then 1 else 0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  change (if (2).Prime ∧ 2 ≠ 2 ∧ jacobiSym (1 : ℤ) 2 = 1 then 1 else 0) +
         ((if (3).Prime ∧ 3 ≠ 2 ∧ jacobiSym (1 : ℤ) 3 = 1 then 1 else 0) + 0) = 1
  norm_num

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  change (if (5).Prime ∧ 5 ≠ 2 ∧ jacobiSym (2 : ℤ) 5 = 1 then 1 else 0) +
         ((if (6).Prime ∧ 6 ≠ 2 ∧ jacobiSym (2 : ℤ) 6 = 1 then 1 else 0) +
         ((if (7).Prime ∧ 7 ≠ 2 ∧ jacobiSym (2 : ℤ) 7 = 1 then 1 else 0) +
         ((if (8).Prime ∧ 8 ≠ 2 ∧ jacobiSym (2 : ℤ) 8 = 1 then 1 else 0) + 0))) = 1
  norm_num

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide +native

/--
Conjecture: $a(n) > 0$ for all $n > 0$.
- _Zhi-Wei Sun_, Dec 29 2012
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : 0 < a n := by
  sorry

end OeisA185150
