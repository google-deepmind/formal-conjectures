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
# Number of primes $< n^2$

Number of primes strictly less than $n^2$.

*References:*
- [A038107](https://oeis.org/A038107)-/

namespace OeisA38107

/-- Number of primes strictly less than $n^2$. -/
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by
  decide

/--
Conjecture: all the numbers $\sum_{i=j}^k \frac{1}{a(i)}$ with $1 < j \le k$ have pairwise distinct
fractional parts.
- Zhi-Wei Sun, Sep 24 2015
-/
@[category research open, AMS 11]
theorem conjecture (j k j' k' : ℕ)
    (hj : 1 < j) (hjk : j ≤ k) (hj' : 1 < j') (hj'k' : j' ≤ k')
    (h_eq : Int.fract (∑ i ∈ Finset.Icc j k, (1 : ℝ) / (a i : ℝ)) =
            Int.fract (∑ i ∈ Finset.Icc j' k', (1 : ℝ) / (a i : ℝ))) :
    j = j' ∧ k = k' := by
  sorry

end OeisA38107
