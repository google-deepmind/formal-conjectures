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
A234809: $a(n) = |\{0 < k < n: p = k + \phi(n-k) \text{ and } 2(n-p) + 1 \text{ are both prime}\}|$,
where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A234809 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k : ℕ =>
    let p : ℕ := k + Nat.totient (n - k)
    if Nat.Prime p ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0


theorem a_one : A234809 1 = 0 := by
  rfl

theorem a_two : A234809 2 = 0 := by
  rfl

theorem a_three : A234809 3 = 1 := by
  rfl

theorem a_four : A234809 4 = 2 := by
  rfl

/-- Conjecture: a(n) > 0 for all n > 2. -/
theorem oeis_234809_conjecture_0 (n : ℕ) (hn : n > 2) : A234809 n > 0 :=
  by sorry
