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
A275027: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}$.
-/
def A275027 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n - k) k))

theorem a_zero : A275027 0 = 1 := by
  rfl

theorem a_one : A275027 1 = 1 := by
  decide

theorem a_two : A275027 2 = 5 := by
  decide

theorem a_three : A275027 3 = 19 := by
  decide

open Padic

/-- A275027 Conjecture: For any prime p > 5 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
theorem oeis_275027_conjecture_0
    {p : ℕ} (hp : Nat.Prime p) (hp_gt_5 : p > 5)
    {n : ℕ} (hn_pos : n > 0) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    let num : ℚ := (A275027 (p * n) : ℚ) - (A275027 n : ℚ)
    let den : ℚ := (p * n : ℚ) ^ 3
    let val_Q : ℚ := num / den
    (val_Q : Padic p) ∈ PadicInt.subring p := by sorry
