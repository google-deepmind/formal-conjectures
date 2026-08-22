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

import Mathlib.Analysis.Convex.Body
import FormalConjectures.Other.LoewnerConjecture
import FormalConjecturesUtil

/-!
# Carathéodory's conjecture

Carathéodory's conjecture says that every sufficiently smooth closed convex surface in
three-dimensional Euclidean space has at least two umbilic points. We state the now-disproved
smooth version and the classical positive result for real-analytic surfaces. We also record that
Loewner's local index conjecture implies Carathéodory's global conjecture. Levent Alpöge announced
the smooth counterexample on 19 August 2026.

*References:*
- [M. Ghomi, *Open Problems in Geometry of Curves and Surfaces*, Problems 8.1 and
  8.2](https://ghomi.math.gatech.edu/Papers/op.pdf)
- [C. J. Titus, *A proof of a conjecture of Loewner and of the conjecture of Carathéodory on
  umbilic points*](https://doi.org/10.1007/BF02392036)
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Set Metric
open scoped ContDiff EuclideanGeometry Manifold

namespace CaratheodoryConjecture

/-- A `C^(k + 1)` parametrized convex surface. Its canonical normal is `C^k` by
`EuclideanHypersurface.contMDiff_sphereNormal`. -/
def IsConvexSphereOfClass (k : WithTop ℕ∞) (F : sphere (0 : ℝ³) 1 → ℝ³) : Prop :=
  ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) (k + 1) F ∧
    Topology.IsEmbedding F ∧
    (∀ p, Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p : TangentSpace (𝓡 2) p →L[ℝ] ℝ³)) ∧
    ∃ K : ConvexBody ℝ³,
      (interior (K : Set ℝ³)).Nonempty ∧ range F = frontier (K : Set ℝ³)

/-- The canonical normal of an `IsConvexSphereOfClass k` surface is of class `C^k`. -/
@[category test, AMS 52 53]
theorem IsConvexSphereOfClass.contMDiff_sphereNormal
    {k : WithTop ℕ∞} {F : sphere (0 : ℝ³) 1 → ℝ³} (hF : IsConvexSphereOfClass k F) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) k (EuclideanHypersurface.sphereNormal F) :=
  EuclideanHypersurface.contMDiff_sphereNormal F hF.1 hF.2.2.1

/-- Carathéodory's conjecture for `IsConvexSphereOfClass k` surfaces. -/
def CaratheodoryConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ F : sphere (0 : ℝ³) 1 → ℝ³, IsConvexSphereOfClass k F →
    ∃ p₁ p₂, p₁ ≠ p₂ ∧
      EuclideanHypersurface.IsUmbilic
        (V := TangentSpace (𝓡 2) p₁) (E := ℝ³)
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p₁ : TangentSpace (𝓡 2) p₁ →L[ℝ] ℝ³)
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (EuclideanHypersurface.sphereNormal F) p₁ :
          TangentSpace (𝓡 2) p₁ →L[ℝ] ℝ³) ∧
      EuclideanHypersurface.IsUmbilic
        (V := TangentSpace (𝓡 2) p₂) (E := ℝ³)
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p₂ : TangentSpace (𝓡 2) p₂ →L[ℝ] ℝ³)
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (EuclideanHypersurface.sphereNormal F) p₂ :
          TangentSpace (𝓡 2) p₂ →L[ℝ] ℝ³)

/-- **The smooth Carathéodory conjecture.**

Every smoothly embedded two-sphere which bounds a convex body has at least two distinct
umbilic points. Alpöge's smooth support function has exactly one umbilic, so the answer is
false. -/
@[category research solved, AMS 52 53,
  formal_proof using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/c0591a2d3c3c8fca852865c8ceecfe4dfb083d10/FormalConjectures/Other/CaratheodoryLoewnerCounterexample.lean#L74"]
theorem caratheodory_conjecture : answer(False) ↔ CaratheodoryConjectureOfClass ∞ := by
  sorry

/-- **The real-analytic Carathéodory conjecture.**

Every real-analytically embedded two-sphere which bounds a convex body has at least two distinct
umbilic points. This is the classical theorem of Hamburger. -/
@[category research solved, AMS 52 53]
theorem caratheodory_conjecture_analytic : CaratheodoryConjectureOfClass ω := by
  sorry

/-- The smooth Loewner conjecture implies the smooth Carathéodory conjecture by the
Poincaré–Hopf index theorem for principal line fields. -/
@[category research solved, AMS 52 53 57]
theorem loewner_implies_caratheodory :
    LoewnerConjecture.LoewnerConjectureOfClass ∞ → CaratheodoryConjectureOfClass ∞ := by
  sorry

end CaratheodoryConjecture
