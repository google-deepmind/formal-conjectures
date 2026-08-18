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


public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Support-restricted Mersenne achievement sets

Statement vocabulary for the subseries of `∑ n, 1 / (2 ^ n - 1)` appearing in
Erdős Problem 257.

Coordinate `k` below carries the positive exponent `k + 1`. Exponent `0` is
excluded: its Mersenne weight `1 / (2 ^ 0 - 1)` is zero under Lean's division
convention, so it contributes nothing to any subseries.
-/

namespace Erdos257

/-- The real Mersenne weight `1 / (2 ^ n - 1)`. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The contribution of coordinate `k`, carrying exponent `k + 1`. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

/-- The Mersenne subseries value coded by a binary digit string. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

/-- Binary digit strings whose nonzero coordinates lie in `J`. -/
def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

/-- The Mersenne digit map restricted to the allowed coordinates `J`. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

/-- All Mersenne subseries sums using only coordinates from `J`. -/
def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

@[simp]
theorem supportedMersenneDigitValue_apply
    (J : Set ℕ) (b : SupportedMersenneDigits J) :
    supportedMersenneDigitValue J b = positiveMersenneDigitValue b.1 :=
  rfl

theorem mem_supportedMersenneAchievementSet_iff (J : Set ℕ) (x : ℝ) :
    x ∈ supportedMersenneAchievementSet J ↔
      ∃ b : SupportedMersenneDigits J, supportedMersenneDigitValue J b = x :=
  Iff.rfl

end Erdos257
