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

/-!
# Conjectures associated with A341254

The constant $r = (2 + \sqrt{5})/2$.

The constant $r^2$.

*References:*
- [A341254](https://oeis.org/A341254)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA341254


open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def r_const : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def r_sq : ℝ := r_const * r_const

/--
A341254: $a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := r_const
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat


@[category test, AMS 11]
lemma a_one : a 1 = 4 := by
  unfold a r_const
  dsimp only
  push_cast
  rw [mul_one]
  have h1 : ⌊(2 + Real.sqrt 5) / 2⌋ = 2 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h1]
  push_cast
  have h2 : ⌊(2 + Real.sqrt 5) / 2 * 2⌋ = 4 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h2]
  rfl

@[category test, AMS 11]
lemma a_two : a 2 = 8 := by
  unfold a r_const
  dsimp only
  push_cast
  have h1 : ⌊(2 + Real.sqrt 5) / 2 * 2⌋ = 4 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h1]
  push_cast
  have h2 : ⌊(2 + Real.sqrt 5) / 2 * 4⌋ = 8 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h2]
  rfl

@[category test, AMS 11]
lemma a_three : a 3 = 12 := by
  unfold a r_const
  dsimp only
  push_cast
  have h1 : ⌊(2 + Real.sqrt 5) / 2 * 3⌋ = 6 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h1]
  push_cast
  have h2 : ⌊(2 + Real.sqrt 5) / 2 * 6⌋ = 12 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h2]
  rfl

@[category test, AMS 11]
lemma a_four : a 4 = 16 := by
  unfold a r_const
  dsimp only
  push_cast
  have h1 : ⌊(2 + Real.sqrt 5) / 2 * 4⌋ = 8 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h1]
  push_cast
  have h2 : ⌊(2 + Real.sqrt 5) / 2 * 8⌋ = 16 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h2]
  rfl

@[category test, AMS 11]
lemma a_five : a 5 = 21 := by
  unfold a r_const
  dsimp only
  push_cast
  have h1 : ⌊(2 + Real.sqrt 5) / 2 * 5⌋ = 10 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h1]
  push_cast
  have h2 : ⌊(2 + Real.sqrt 5) / 2 * 10⌋ = 21 := by
    rw [Int.floor_eq_iff]
    have h5 : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
      norm_num [Real.sqrt_lt, Real.lt_sqrt]
    constructor <;> linarith
  rw [h2]
  rfl


/--
The constant $r = (2 + \sqrt{5})/2$.

The constant $r^2$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/341254.wip.lean#L188"]
theorem a_bounds (n : ℕ) (hn : 1 ≤ n) : (1 / 4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧
    (n : ℝ) * r_sq - (a n : ℝ) < 3 := by
    sorry

end OeisA341254
