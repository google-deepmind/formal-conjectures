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
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Projection bodies

Orthogonal shadow volume uses Lebesgue measure on the orthogonal subspace with
its induced Euclidean structure. The projection body is defined by unit-direction
support bounds. This is the unpolarized projection body used in Petty's conjecture.

Definitions adapted from OpenAI's
[PettyProjectionVolume](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PettyProjectionVolume.lean),
Apache-2.0. Namespace and names were changed.
-/

@[expose] public section

namespace ConvexGeometry

open MeasureTheory
open scoped InnerProductSpace

/-- The orthogonal subspace to a real Euclidean vector. -/
noncomputable def perpendicular {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Submodule.span ℝ {u})ᗮ

/-- Volume of the orthogonal shadow in the induced Euclidean subspace. -/
noncomputable def shadowVolume {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (volume : Measure (perpendicular u)).real
    ((perpendicular u).orthogonalProjectionOnto '' K)

/-- The projection body, with support bounds given by orthogonal shadow volumes. -/
noncomputable def projectionBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ u, ‖u‖ = 1 → ⟪u, x⟫_ℝ ≤ shadowVolume K u}

/-- Projection-body volume divided by the $(n-1)$st power of body volume. -/
noncomputable def projectionRatio {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  volume.real (projectionBody K) / volume.real K ^ (n - 1)

theorem zero_mem_projectionBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    0 ∈ projectionBody K := by
  intro u _
  simp [shadowVolume, Measure.real]

end ConvexGeometry
