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

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise addition of finite intervals
-/

@[expose] public section

open scoped Pointwise

namespace Finset

/-- The sum of `{0, …, m}` and `{0, …, n}` is `{0, …, m + n}`. -/
theorem range_add_range (m n : ℕ) :
    range (m + 1) + range (n + 1) = range (m + n + 1) := by
  ext k
  simp only [mem_add, mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    lia
  · intro hk
    by_cases hkm : k ≤ m
    · exact ⟨k, by lia, 0, by lia, by simp⟩
    · exact ⟨m, by lia, k - m, by lia, by lia⟩

end Finset
