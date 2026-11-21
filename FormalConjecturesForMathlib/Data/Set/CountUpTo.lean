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

public import Mathlib.Order.Interval.Set.Nat

/-!
# Counting positive integers in a set

`Set.countUpTo A N` counts the elements of `A` in the interval `[1, N]`.
-/

@[expose] public section

namespace Set

/-- The number of elements of a set of natural numbers in $\{1,\ldots,N\}$. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Icc 1 N).ncard

@[simp]
theorem countUpTo_empty (N : ℕ) : countUpTo ∅ N = 0 := by
  simp [countUpTo]

@[simp]
theorem countUpTo_univ (N : ℕ) : countUpTo univ N = N := by
  simp [countUpTo]

@[simp]
theorem countUpTo_zero (A : Set ℕ) : countUpTo A 0 = 0 := by
  simp [countUpTo]

end Set
