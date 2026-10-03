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
# Number of distinct sums of distinct proper divisors of $n$

The sequence $a(n)$ counts the number of distinct sums of non-empty subsets of the proper divisors
of $n$.

*References:*
- [A193279](https://oeis.org/A193279)
- [OEIS Open](https://arxiv.org/abs/2608.11941)
  by *Tom Adamczewski*, arXiv:2608.11941 (2026)
-/

namespace OeisA193279

/--
Number of distinct sums of distinct proper divisors of $n$ (excluding the empty sum $0$).
-/
def a (n : ℕ) : ℕ :=
  (n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x)).card - 1

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by decide

/--
Conjecture: If $a(n) = n$, is $n$ necessarily an even perfect number?
- _Michael Engling_, Jul 20 2011
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) (h : a n = n) : Nat.Perfect n ∧ Even n := by
  sorry

end OeisA193279
