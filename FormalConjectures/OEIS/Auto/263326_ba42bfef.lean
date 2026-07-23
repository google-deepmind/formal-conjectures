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

open Nat Rat Finset

/--
A263326: Denominator of the rational number $\sum_{d|n} \frac{1}{d+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + 1 : ℚ)⁻¹).den


theorem a_one : a 1 = 2 := by sorry

theorem a_two : a 2 = 6 := by sorry

theorem a_three : a 3 = 4 := by sorry

theorem a_four : a 4 = 30 := by sorry

/--
The rational number $\sum_{d|n} \frac{1}{(d+k)^s}$.
-/
noncomputable def S (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast)⁻¹ ^ s.cast

/--
Conjecture: For any positive integers $k$ and $s$, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (for $n = 1,2,3, \dots$)
have pairwise distinct fractional parts, and none of them is an integer.
-/
theorem oeis_263326_conjecture_0 (k s : ℕ) (hk : k > 0) (hs : s > 0) :
  (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
    Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s)) :=
by sorry
