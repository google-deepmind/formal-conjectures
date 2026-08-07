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

open Nat Finset

/--
A181830: The number of positive integers $\le n$ that are strongly prime to $n$.
$k$ is strongly prime to $n$ if and only if $k$ is relatively prime to $n$ and $k$ does not divide $n - 1$.
-/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else totient n - (divisors (n - 1)).card


theorem a_zero : a 0 = 0 := by
  rfl

theorem a_one : a 1 = 0 := by
  trivial

theorem a_two : a 2 = 0 := by
  rfl

theorem a_three : a 3 = 0 := by
  rfl

noncomputable section

/-- The number of cardboard braids that work with n slots.
    This is an informal definition from OEIS A181830 and is introduced as a noncomputable constant
    to formalize the conjecture. -/
axiom cardboard_braids_count : ℕ → ℕ

/-- It is conjectured (see Scroggs link) that a(n) is also the number of cardboard braids that work with n slots. - Matthew Scroggs, Sep 23 2017 -/
theorem oeis_181830_conjecture_0 (n : ℕ) : a n = cardboard_braids_count n := by
  sorry

end
