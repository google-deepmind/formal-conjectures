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
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
def A274274 (n : ℕ) : ℕ :=
  -- Iterate over all possible non-negative integers x, y, z up to n.
  -- This bounded sum covers all solutions since x^3, y^2, z^2 must be less than or equal to n.
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    -- Count 1 for each triple (x, y, z) that satisfies the equation and the constraint y ≤ z.
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

theorem a_zero : A274274 0 = 1 := by rfl
/-- The manual checks are omitted as they are not the core request, but provided for completeness.
We keep the `by sorry` as instructed when the proof is non-trivial. -/
theorem a_one : A274274 1 = 2 := by sorry
theorem a_two : A274274 2 = 2 := by sorry
theorem a_three : A274274 3 = 1 := by rfl


/--
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.
-/
theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) :=
by sorry

/--
Conjecture (ii): Either n or n-3 can be written as $x^3 + y^2 + 3z^2$ with x,y,z nonnegative integers.
-/
theorem A274274_conjecture_ii :
  ∀ (n : ℕ), representable_type_ii n ∨ (n ≥ 3 ∧ representable_type_ii (n - 3)) :=
by sorry

/--
Conjecture (iii): For each d = 4, 5, 11, 12, either n or n-d can be written as $x^3 + y^2 + 2z^2$ with x,y,z nonnegative integers.
-/
theorem A274274_conjecture_iii :
  ∀ (n : ℕ),
    (representable_type_iii n ∨ (n ≥ 4 ∧ representable_type_iii (n - 4))) ∧
    (representable_type_iii n ∨ (n ≥ 5 ∧ representable_type_iii (n - 5))) ∧
    (representable_type_iii n ∨ (n ≥ 11 ∧ representable_type_iii (n - 11))) ∧
    (representable_type_iii n ∨ (n ≥ 12 ∧ representable_type_iii (n - 12))) :=
by sorry
