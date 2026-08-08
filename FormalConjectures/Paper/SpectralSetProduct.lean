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

import FormalConjecturesUtil
import Mathlib.Analysis.Convex.Body

/-!
# Spectral products with a convex factor

This file formalizes Problem 7.2 from Kolountzakis, Lev, and Matolcsi:
if a product `A × B` is spectral and `A` is a convex body, must `B` be spectral?

*References:*
* [KLM2023] Mihail N. Kolountzakis, Nir Lev, and Máté Matolcsi,
  "Spectral sets and weak tiling." https://arxiv.org/abs/2209.04540
-/

open MeasureTheory

namespace SpectralSetProduct

/-- The product of two Euclidean sets, represented by consecutive coordinate blocks. -/
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}

/-- Problem 7.2 in [KLM2023]: if `A × B` is spectral, where `A` is a convex body and
`B` is bounded and measurable, then `B` is spectral. -/
@[category research open, AMS 42 46]
theorem isSpectral_right_of_product_of_convexBody :
    ∀ (n m : ℕ), 0 < n → 0 < m →
      ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
        Bornology.IsBounded B → MeasurableSet B →
          isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B := by
  sorry

end SpectralSetProduct
