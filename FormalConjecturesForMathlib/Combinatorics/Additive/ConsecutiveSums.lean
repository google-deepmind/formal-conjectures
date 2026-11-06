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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Prod

/-!
# Consecutive sums of a finite sequence
-/

@[expose] public section

variable {M : Type*} [AddCommMonoid M] [DecidableEq M]

/-- The set of sums $\sum_{u\leq i\leq v}a_i$ of nonempty consecutive blocks of a finite
sequence `a`. -/
def consecutiveSums {k : ℕ} (a : Fin k → M) : Finset M :=
  (Finset.univ.filter fun p : Fin k × Fin k => p.1 ≤ p.2).image
    fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i

/-- An empty sequence has no nonempty consecutive blocks. -/
@[simp] theorem consecutiveSums_empty (a : Fin 0 → M) : consecutiveSums a = ∅ := by
  simp [consecutiveSums]
