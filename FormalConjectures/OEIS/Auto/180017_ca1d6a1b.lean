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

open Nat

/--
A180017: Difference of sums of digits of $n$ in ternary and in binary.
$$a(n) = \left(\sum \text{digits}_3(n)\right) - \left(\sum \text{digits}_2(n)\right)$$
-/
def a (n : ℕ) : ℤ :=
  Int.ofNat (Nat.digits 3 n |>.sum) - Int.ofNat (Nat.digits 2 n |>.sum)


theorem a_zero : a 0 = 0 := by
  norm_num[a]

theorem a_one : a 1 = 0 := by
  norm_num[a]

theorem a_two : a 2 = 1 := by
  norm_num[a]

theorem a_three : a 3 = -1 := by
  symm
  norm_num[a]


/--
%C A180017 This sequence is positive on average, since 1/log(3) > 1/log(4). Do all integers appear infinitely often? - _Charles R Greathouse IV_, Feb 07 2013
The conjecture asks if for every integer $z$, the set of natural numbers $n$ such that $a(n) = z$ is infinite.
-/
theorem oeis_180017_conjecture_0 :
  ∀ z : ℤ, Set.Infinite { n : ℕ | a n = z } := by sorry
