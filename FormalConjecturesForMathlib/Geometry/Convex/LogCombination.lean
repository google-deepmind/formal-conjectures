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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Logarithmic combination of convex bodies

The support function and logarithmic Wulff combination used in the logarithmic
Brunn–Minkowski conjecture.
-/

@[expose] public section

namespace ConvexGeometry

open scoped InnerProductSpace

/-- The support function $h_K(u) = \sup_{x \in K}\langle x,u\rangle$. -/
noncomputable def support {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => ⟪x, u⟫_ℝ) '' K)

/-- The logarithmic Wulff combination, defined by its supporting half-spaces. -/
noncomputable def logCombination {n : ℕ} (K L : Set (EuclideanSpace ℝ (Fin n)))
    (t : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ u, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ (support K u) ^ (1 - t) * (support L u) ^ t}

theorem mem_logCombination_iff {n : ℕ} (K L : Set (EuclideanSpace ℝ (Fin n)))
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ logCombination K L t ↔
      ∀ u, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ (support K u) ^ (1 - t) * (support L u) ^ t :=
  Iff.rfl

end ConvexGeometry
