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
A369462: Number of representations of $12n-1$ as a sum $(p \cdot q + p \cdot r + q \cdot r)$ with three odd primes $p \le q \le r$.
-/
noncomputable def A369462 (n : ℕ) : ℕ :=
  if 1 ≤ n then
    let N : ℕ := 12 * n - 1
    -- N is the target number. Since p*q < N, p, q, r are all bounded by N.
    let B := N
    let search_range := range (B + 1)
    let search_space := search_range.product (search_range.product search_range)

    (search_space.filter (fun t : ℕ × ℕ × ℕ =>
      let p := t.fst
      let q := t.snd.fst
      let r := t.snd.snd
      -- 1. All must be odd primes (Prime and not equal to 2)
      p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ r.Prime ∧ r ≠ 2 ∧
      -- 2. Order and sum constraint.
      p ≤ q ∧ q ≤ r ∧ p * q + p * r + q * r = N
    )).card
  else
    0


theorem a_one : A369462 1 = 0 := by
  sorry

theorem a_two : A369462 2 = 0 := by
  sorry

theorem a_three : A369462 3 = 0 := by
  sorry

theorem a_four : A369462 4 = 0 := by
  sorry

/--
Conjecture A369462: Is there only a finite number of 0's in this sequence?
-/
theorem oeis_369462_conjecture_0 : {n : ℕ | A369462 n = 0}.Finite := by
  sorry
