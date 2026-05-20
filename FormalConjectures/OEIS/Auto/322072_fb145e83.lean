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

open BigOperators

/--
The sequence A322072: Row sums of the triangle A322071.
$$a(n) = \sum_{k=1}^n \left\lfloor \frac{2n^k}{k^k} \right\rfloor$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    let term_q : ℚ := (num : ℚ) / (den : ℚ)
    (Rat.floor term_q).toNat


theorem a_one : a 1 = 2 := by
  simp_all[a]
  simp_all[ Rat.floor]

theorem a_two : a 2 = 6 := by
  norm_num[a]
  norm_num +decide only [ Finset.sum_Icc_succ_top, false, Finset.Icc_self, Finset.sum_singleton]

theorem a_three : a 3 = 12 := by
  norm_num[a]
  refine show∑ a ∈ _,⌊_/ (@_:ℚ)⌋.toNat = _ by·norm_cast

theorem a_four : a 4 = 22 := by
  rw [←eq_comm, a]
  use(( Finset.sum_Icc_succ_top (by decide) _).trans (.trans (by rw [ Finset.sum_Icc_succ_top (by decide), Finset.sum_Icc_succ_top (by decide), Finset.Icc_self, Finset.sum_singleton]) (by norm_num+decide[ Rat.floor]))).symm


/--
OEIS A322072 Conjecture: The difference $a(n + 1) - a(n)$ between two consecutive terms is not a perfect square except for $n = 1, 5$ and $6$.
-/
theorem oeis_322072_conjecture_0 {n : ℕ} (hn : 1 ≤ n) :
  (∃ m : ℕ, a (n + 1) - a n = m ^ 2) ↔ n = 1 ∨ n = 5 ∨ n = 6 :=
by sorry
