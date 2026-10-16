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
module

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 66

*Reference:* [Ben Green's Open Problem 66](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8)
-/

@[expose] public section

open Filter

namespace Green66

/-- A natural number is a sum of two squares if it can be written as `a ^ 2 + b ^ 2`. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/--
Is there always a sum of two squares between $X - \frac{1}{10}X^{1/4}$ and $X$?
We formalize this as an eventual statement for sufficiently large real $X$.
-/
@[category research open, question, AMS 11]
theorem green_66 :
    ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - (1 / 10 : ℝ) * X ^ (1 / 4 : ℝ)) X := by
  sorry

/--
Green notes that a well-known, almost trivial argument gives an $O(X^{1/4})$ bound on the left.
-/
@[category research solved, AMS 11]
theorem green_66.variants.trivial_bound :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X := by
  -- Subtract the greatest square `u ^ 2` below `X`, then the greatest square `v ^ 2`
  -- below `X - u ^ 2`.
  refine ⟨5, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  set s : ℝ := X ^ (1 / 4 : ℝ) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hX (by norm_num)
  have hs4 : s ^ 4 = X := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hs0 : 0 ≤ s := by linarith
  have hsq0 : 0 ≤ s ^ 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌊s ^ 2⌋₊ := ⟨_, rfl⟩
  have ha1 : (a : ℝ) ≤ s ^ 2 := ha ▸ Nat.floor_le hsq0
  have ha2 : s ^ 2 < a + 1 := ha ▸ Nat.lt_floor_add_one _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  set r : ℝ := X - (a : ℝ) ^ 2 with hr
  have hr0 : 0 ≤ r := by nlinarith
  have hr1 : r < 2 * s ^ 2 := by
    have h1 : r = (s ^ 2 - a) * (s ^ 2 + a) := by rw [hr, ← hs4]; ring
    have h2 : (s ^ 2 - a) * (s ^ 2 + a) < 1 * (s ^ 2 + a) :=
      mul_lt_mul_of_pos_right (by linarith) (by nlinarith)
    linarith
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊Real.sqrt r⌋₊ := ⟨_, rfl⟩
  have hb1 : (b : ℝ) ≤ Real.sqrt r := hb ▸ Nat.floor_le (Real.sqrt_nonneg r)
  have hb2 : Real.sqrt r < b + 1 := hb ▸ Nat.lt_floor_add_one _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  have hbr : (b : ℝ) ^ 2 ≤ r := by nlinarith [Real.sqrt_nonneg r]
  have hrb : r < ((b : ℝ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg r]
  have hb3 : (b : ℝ) < 2 * s := by nlinarith
  refine ⟨a ^ 2 + b ^ 2, ⟨a, b, rfl⟩, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith

end Green66
