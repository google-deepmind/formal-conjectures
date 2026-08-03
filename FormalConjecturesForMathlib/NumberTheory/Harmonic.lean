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


public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Block harmonic sums

Mathlib's `harmonic n` is the initial harmonic sum `∑_{1 ≤ k ≤ n} 1 / k`, valued in `ℚ`.
Several problems instead need the *block* sum `∑_{n ≤ k ≤ m} 1 / k`, and need it in `ℝ` as
often as in `ℚ`, so `harmonicBlock` is stated over an arbitrary division ring.

## Main definitions

* `harmonicBlock`: the block harmonic sum `∑_{n ≤ k ≤ m} 1 / k`.

## Main results

* `harmonicBlock_eq_zero_of_lt`: the block sum is empty when `m < n`.
* `harmonicBlock_one`: `harmonicBlock ℚ 1 n` is Mathlib's `harmonic n`.
* `Rat.cast_harmonicBlock`: the cast of the rational block sum is the block sum.
-/

/-- The block harmonic sum $\sum_{n\leq k\leq m}\frac{1}{k}$, valued in a division ring `K`.
For `n = 1` this is Mathlib's `harmonic`, see `harmonicBlock_one`. -/
def harmonicBlock (K : Type*) [DivisionRing K] (n m : ℕ) : K := ∑ k ∈ Finset.Icc n m, (k : K)⁻¹

variable {K : Type*} [DivisionRing K] (n m : ℕ)

theorem harmonicBlock_eq_sum_one_div :
    harmonicBlock K n m = ∑ k ∈ Finset.Icc n m, 1 / (k : K) := by
  simp [harmonicBlock, one_div]

@[simp]
theorem harmonicBlock_eq_zero_of_lt (h : m < n) : harmonicBlock K n m = 0 := by
  simp [harmonicBlock, Finset.Icc_eq_empty_of_lt h]

theorem harmonicBlock_succ_top (h : n ≤ m + 1) :
    harmonicBlock K n (m + 1) = harmonicBlock K n m + ((m : K) + 1)⁻¹ := by
  simp [harmonicBlock, Finset.sum_Icc_succ_top h]

/-- The block sum starting at `1` is Mathlib's harmonic number. -/
theorem harmonicBlock_one (n : ℕ) : harmonicBlock ℚ 1 n = harmonic n := by
  induction n with
  | zero => simp [harmonicBlock]
  | succ n ih => rw [harmonicBlock_succ_top _ _ (by omega), ih, harmonic_succ]; push_cast; ring

@[simp, norm_cast]
theorem Rat.cast_harmonicBlock [CharZero K] :
    ((harmonicBlock ℚ n m : ℚ) : K) = harmonicBlock K n m := by
  rw [harmonicBlock, harmonicBlock, ← Rat.coe_castHom (α := K), map_sum]
  simp
