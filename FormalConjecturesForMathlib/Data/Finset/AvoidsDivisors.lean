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

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Divisibility.Basic

@[expose] public section

namespace Finset

/-- The integers in `{1, …, x}` not divisible by any element of `A`. -/
def avoidsDivisors (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun m => ∀ a ∈ A, ¬ a ∣ m)

@[simp]
lemma mem_avoidsDivisors {A : Finset ℕ} {x m : ℕ} :
    m ∈ avoidsDivisors A x ↔ m ∈ Icc 1 x ∧ ∀ a ∈ A, ¬ a ∣ m := by
  simp [avoidsDivisors]

lemma avoidsDivisors_empty (x : ℕ) :
    avoidsDivisors ∅ x = Icc 1 x := by
  simp [avoidsDivisors]

end Finset
