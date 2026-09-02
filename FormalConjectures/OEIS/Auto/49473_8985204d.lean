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

open Real

/--
A049473: Nearest integer to $n/\sqrt{2}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor ((n : ℝ) / sqrt 2 + 1 / 2)).toNat


theorem a_zero : a 0 = 0 := by
  sorry

theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 1 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry

/-- $\zeta(3)$ is the Apery's constant. -/
noncomputable def zeta_three_real : ℝ :=
  (riemannZeta 3).re

/--
Let $s(n) = \zeta(3) - \sum_{k=1}^{n} 1/k^3$.
-/
noncomputable def s (n : ℕ) : ℝ :=
  zeta_three_real - Finset.sum (Finset.range n) (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℝ) ^ 3))

open Finset

noncomputable def phi : ℝ := (1 + sqrt 5) / 2

/--
A001954: Nonhomogeneous Beatty sequence $\lfloor k\phi \rfloor$ for $k \ge 1$.
-/
noncomputable def A001954 : Set ℕ :=
  {n | ∃ k : ℕ, 0 < k ∧ n = (Int.floor ((k : ℝ) * phi)).toNat}

/--
A001953: Nonhomogeneous Beatty sequence $\lfloor k\phi^2 \rfloor$ for $k \ge 1$.
-/
noncomputable def A001953 : Set ℕ :=
  {n | ∃ k : ℕ, 0 < k ∧ n = (Int.floor ((k : ℝ) * phi ^ 2)).toNat}

/--
oeis_49473_conjecture_0: Let s(n) = zeta(3) - Sum_{k=1..n} 1/k^3.
Conjecture: for n >=1, s(a(n)) < 1/n^2 < s(a(n)-1), and the difference sequence of A049473
consists solely of 0's and 1, in positions given by the nonhomogeneous Beatty sequences
A001954 and A001953, respectively.
-/
theorem oeis_49473_conjecture_0 :
  (∀ (n : ℕ), 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
  (∀ (n : ℕ), 1 ≤ n →
    let diff : ℕ := a n - a (n - 1);
    (diff = 1 ↔ n ∈ A001954) ∧ (diff = 0 ↔ n ∈ A001953)) :=
by sorry
