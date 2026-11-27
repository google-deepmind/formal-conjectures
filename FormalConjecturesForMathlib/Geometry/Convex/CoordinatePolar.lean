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
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Coordinate polar

The one-sided polar in standard real coordinates, used in the Mahler conjecture.
-/

@[expose] public section

namespace ConvexGeometry

/-- The polar $K^\circ$ in standard real coordinates. -/
def coordinatePolar {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {p | ∀ v ∈ K, (∑ i, p i * v i) ≤ 1}

theorem zero_mem_coordinatePolar {n : ℕ} (K : Set (Fin n → ℝ)) :
    0 ∈ coordinatePolar K := by
  simp [coordinatePolar]

end ConvexGeometry
