/-
Copyright 2025 The Formal Conjectures Authors.

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


public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

@[expose] public section

-- TODO(mercuris): define a recursive version of this for better usability?
-- TODO(mercuris): add `Real.iteratedLogb` for general bases
/-- The iterated logarithm of `x` is the number of times the natural logarithm
must be iteratively applied before the result is less than or equal to `1`.
Reference: https://en.wikipedia.org/wiki/Iterated_logarithm -/
noncomputable def Real.iteratedLog (x : ℝ) : ℕ :=
  sInf { (n : ℕ) | Real.log^[n] x ≤ 1 }

/-- The iterated logarithm of a natural number in base `b`: the number of times `Nat.log b` must
be iteratively applied to `n` before the result is at most `1`. -/
def Nat.iteratedLog (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.iteratedLog b (Nat.log b (n + 2)) + 1
termination_by n => n
decreasing_by exact Nat.log_lt_self b (by omega)

@[simp]
theorem Nat.iteratedLog_zero (b : ℕ) : Nat.iteratedLog b 0 = 0 := by
  simp [Nat.iteratedLog]

@[simp]
theorem Nat.iteratedLog_one (b : ℕ) : Nat.iteratedLog b 1 = 0 := by
  simp [Nat.iteratedLog]

theorem Nat.iteratedLog_of_two_le (b : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    Nat.iteratedLog b n = Nat.iteratedLog b (Nat.log b n) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.iteratedLog]

theorem Real.iteratedLog_eq_zero_of_le {x : ℝ} (hx : x ≤ 1) :
    Real.iteratedLog x = 0 := by
  simpa [iteratedLog] using Or.inl hx

theorem Real.iteratedLog_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    Real.iteratedLog x = 0 :=
  Real.iteratedLog_eq_zero_of_le (by linarith)

theorem iteratedLog_two : Real.iteratedLog 2 = 1 := by
  simp [Real.iteratedLog]
  have : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show 0 < 2 by norm_num)
    norm_num
  rw [Nat.sInf_def ⟨1, this⟩]
  exact (Nat.find_eq_iff _).2 ⟨this, fun n hn => by simp [Nat.lt_one_iff.1 hn]⟩

theorem iteratedLog_four : Real.iteratedLog 4 = 2 := by
  simp [Real.iteratedLog]
  have : Real.log^[2] 4 ≤ 1 := by
    have h_ne_zero : Real.log √4 ≠ 0 := by simp; linarith [Real.sqrt_nonneg 4]
    have : Real.log 4 ≤ 2 := by
      have := mul_eq_of_eq_mul_inv₀ h_ne_zero <| div_eq_mul_inv _ (2 : ℝ) ▸ (Real.log_sqrt (show 0 ≤ 4 by linarith))
      rw [← this]
      norm_num
      convert! Real.log_le_sub_one_of_pos (show 0 < 2 by norm_num)
      norm_num
    have : Real.log 4 - 1 ≤ 1 := by convert sub_le_sub_right this 1; norm_num
    exact le_trans (Real.log_le_sub_one_of_pos (Real.log_pos <| by norm_num)) this
  rw [Nat.sInf_def ⟨2, by aesop⟩]
  refine (Nat.find_eq_iff _).2 ⟨by aesop, fun n hn => ?_⟩
  interval_cases n; simp
  simp [Real.lt_log_iff_exp_lt]
  linarith [Real.exp_one_lt_d9]
