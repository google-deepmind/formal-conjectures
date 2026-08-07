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

open Finset Nat

/--
A117531: Number of primes in the $n$-th row of the triangle in A117530.
The elements of the $n$-th row of A117530 are $T(n, k) = k^2 - k + p_n$ for $1 \le k \le n$,
where $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is defined for n >= 1. Icc 1 0 is empty, correctly yielding 0 for n=0.
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  -- We count how many terms T(n, k) are prime for k in {1, 2, ..., n}.
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))


theorem a_one : a 1 = 1 := by
  simp_all[a]
  rfl

theorem a_two : a 2 = 2 := by
  norm_num[a ·]
  constructor

theorem a_three : a 3 = 3 := by
  norm_num[a ·]
  rfl

theorem a_four : a 4 = 3 := by
  norm_num[a ·]
  try decide


/--
Conjecture: $a(n) < n$ for $n > 13$.
-/
theorem oeis_117531_conjecture_0 (n : ℕ) (h : n > 13) : a n < n := by
  sorry
