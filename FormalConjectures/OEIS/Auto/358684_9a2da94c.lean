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
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  let pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)


theorem a_zero : a 0 = 0 := by
  sorry

theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 0 := by
  sorry


/--
a(14) is probably equal to 16208; a(15) to a(19) are 32738, 65507, 131028, 262121, 524252;
a(20) is unknown; a(21) to a(23) are 2097110, 4194189, 8388581; a(24) is unknown.
-/
theorem oeis_358684_conjecture_1 :
    a 14 = 16208 ∧
    a 15 = 32738 ∧
    a 16 = 65507 ∧
    a 17 = 131028 ∧
    a 18 = 262121 ∧
    a 19 = 524252 ∧
    a 21 = 2097110 ∧
    a 22 = 4194189 ∧
    a 23 = 8388581 := by
  sorry
