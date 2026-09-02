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

/--
A069922: Number of primes $p$ such that $n^n \le p \le n^n + n^2$.
-/
def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card


theorem a_one : A069922 1 = 1 := by sorry
theorem a_two : A069922 2 = 2 := by sorry
theorem a_three : A069922 3 = 2 := by sorry
theorem a_four : A069922 4 = 4 := by sorry

/--
Question: for any n>0, is there at least one prime p such that n^n <= p <= n^n + n^2?
In this case, that would be stronger than the Schinzel conjecture: "for m > 1 there's at least one prime p such that m <= p <= m + log(m)^2" since n^2 < log(n^n)^2 = n^2*log(n)^2.
-/
theorem oeis_69922_conjecture_0 : ∀ (n : ℕ), n > 0 → A069922 n > 0 :=
by sorry
