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

open Nat Set

/--
A034694: Smallest prime $\equiv 1 \pmod n$.
$$a(n) = \min \{p \in \mathbb{P} \mid p \equiv 1 \pmod n \}$$
-/
noncomputable def A034694 (n : ℕ) : ℕ :=
  -- The set infimum, sInf, gives the smallest element of the set of natural numbers.
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}


theorem a_one : A034694 1 = 2 := by
  simp_rw [A034694]
  exact IsLeast.csInf_eq ⟨by decide, fun and true => true.1.two_le⟩

theorem a_two : A034694 2 = 3 := by
  delta A034694
  apply((Nat.isLeast_find ⟨3,by decide⟩ ) ).csInf_eq

theorem a_three : A034694 3 = 7 := by
  norm_num [A034694]
  apply Nat.isLeast_find ⟨7, by decide⟩ |>.csInf_eq

theorem a_four : A034694 4 = 5 := by
  norm_num [A034694]
  apply Nat.isLeast_find ⟨5, by decide⟩ |>.csInf_eq

/-- OEIS A034694 Conjecture: a(n) < n^2 for n > 1. - Thomas Ordowski, Dec 19 2016 -/
theorem oeis_34694_conjecture_0 (n : ℕ) (h : 1 < n) :
  A034694 n < n ^ 2 := by sorry
