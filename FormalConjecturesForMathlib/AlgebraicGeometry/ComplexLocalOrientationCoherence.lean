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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexLocalOrientation
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifoldOrientation
public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance

/-!
# Coherence of the complex local orientation

The local class constructed from the preferred algebraic chart does not depend on which preferred
chart containing the point is used.  The proof computes the derivative of the actual compressed
transition appearing in `localClassOfChart`: its three factors are the first radial compression,
the complex tangent-coordinate equivalence, and the inverse radial compression.  All three are
injective complex-linear maps, so nonlinear local-class invariance applies.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The normalized local homology classes obtained from any two preferred algebraic charts
containing a point coincide. -/
theorem localClassOfChart_localChart_eq
    [SmoothOfRelativeDimension d X.hom]
    (z z' q : ComplexPoint X)
    (hq : q ∈ (localChart X d z).source)
    (hq' : q ∈ (localChart X d z').source) :
    localClassOfChart d (localChart X d z) q hq =
      localClassOfChart d (localChart X d z') q hq' := by
  let T : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    tangentCoordChange 𝓘(ℂ, Fin d → ℂ) z z' q
  have hoverlap : q ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source ∩
      (extChartAt 𝓘(ℂ, Fin d → ℂ) z').source := by
    rw [extChartAt_source, extChartAt_source]
    exact ⟨hq, hq'⟩
  have hraw : HasFDerivAt
      (fun v ↦ localChart X d z' ((localChart X d z).symm v)) T
      (localChart X d z q) := by
    have h := hasFDerivWithinAt_tangentCoordChange
      (I := 𝓘(ℂ, Fin d → ℂ)) hoverlap
    apply (piHasFDerivAt_iff_normed d _ T (localChart X d z q)).mpr
    simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [] with v
    change localChart X d z' ((localChart X d z).symm v) =
      (chartAt (Fin d → ℂ) z') ((chartAt (Fin d → ℂ) z).symm v)
    rfl
  have hT : Function.Injective T := by
    intro a b hab
    apply (tangentCoordChangeEquiv 𝓘(ℂ, Fin d → ℂ) z z' q).injective
    have hqchart : q ∈ (chartAt (Fin d → ℂ) z).source := hq
    have hqchart' : q ∈ (chartAt (Fin d → ℂ) z').source := hq'
    simpa only [T, tangentCoordChangeEquiv_apply hqchart hqchart'] using hab
  exact localClassOfChart_eq_of_hasFDerivAt_transition d
    (localChart X d z) (localChart X d z') q hq hq' T hT hraw

/-- The canonical pointwise class can equivalently be computed using the preferred algebraic
chart centered at any other point whose source contains the point in question. -/
theorem complexLocalOrientation_eq_localClassOfChart_localChart
    [SmoothOfRelativeDimension d X.hom]
    (z q : ComplexPoint X)
    (hq : q ∈ (localChart X d z).source) :
    complexLocalOrientation X d q =
      localClassOfChart d (localChart X d z) q hq := by
  rw [complexLocalOrientation_eq_localClassOfChart]
  exact localClassOfChart_localChart_eq X d q z q
    (mem_localChart_source X d q) hq

end AlgebraicGeometry.ComplexPoint
