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
A248123: Least integer $m > 0$ such that $\gcd(m,n) = 1$ and $m \cdot n \mid C(m+n)$,
where $C(k)$ refers to the $k$-th Catalan number $\binom{2k}{k}/(k+1)$.
-/
noncomputable def A248123 (n : ℕ) : ℕ :=
  -- Define the $k$-th Catalan number $C(k)$ explicitly.
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)

  -- The sequence value a(n) is the least element (infimum) of the set of candidates.
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}


theorem a_one : A248123 1 = 1 := by
  simp_all[A248123]
  apply Nat.isLeast_find ⟨1, by decide⟩ |>.csInf_eq

theorem a_two : A248123 2 = 3 := by
  nontriviality
  rw[A248123]
  apply Nat.isLeast_find ⟨3, by decide⟩ |>.csInf_eq

theorem a_three : A248123 3 = 2 := by
  inhabit Real
  rw[A248123]
  apply Nat.isLeast_find ⟨2, by decide⟩ |>.csInf_eq

theorem a_four : A248123 4 = 21 := by
  delta A248123
  apply Nat.isLeast_find ⟨21, (by decide)⟩ |>.csInf_eq

/-- A248123 Conjecture: a(n) exists for all n > 0. -/
theorem oeis_248123_conjecture_0 (n : ℕ) (hn : n > 0) : A248123 n > 0 := by sorry
