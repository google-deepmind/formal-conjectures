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
import FormalConjectures.Other.LoewnerConjecture

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

/-- A parametrized convex surface whose canonical normal is of class `C^k`.

The canonical normal is constructed from the derivative of `F` by a globally
orientation-corrected cross product. Its orthogonality is built into the construction, while the
injective differential makes it a unit vector. For finite `k`, requiring this normal to be `C^k`
is stronger than requiring only `F` to be `C^k`. The range condition identifies the surface with
the boundary of a compact convex body with nonempty interior. -/
def IsConvexSphereOfClass (k : WithTop ℕ∞) (F : sphere (0 : ℝ³) 1 → ℝ³) : Prop :=
  ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) k F ∧
    Topology.IsEmbedding F ∧
    (∀ p, Function.Injective (EuclideanHypersurface.sphereAmbientMfderiv F p)) ∧
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) k (EuclideanHypersurface.sphereNormal F) ∧
    ∃ K : Set ℝ³,
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ range F = frontier K

/-- Carathéodory's conjecture for convex surfaces with a `C^k` canonical normal constructed
from the derivative of the parametrization. -/
def CaratheodoryConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ F : sphere (0 : ℝ³) 1 → ℝ³, IsConvexSphereOfClass k F →
    ∃ p₁ p₂, p₁ ≠ p₂ ∧
      EuclideanHypersurface.IsUmbilic
        (EuclideanHypersurface.sphereAmbientMfderiv F p₁)
        (EuclideanHypersurface.sphereAmbientMfderiv
          (EuclideanHypersurface.sphereNormal F) p₁) ∧
      EuclideanHypersurface.IsUmbilic
        (EuclideanHypersurface.sphereAmbientMfderiv F p₂)
        (EuclideanHypersurface.sphereAmbientMfderiv
          (EuclideanHypersurface.sphereNormal F) p₂)

/-- **The smooth Carathéodory conjecture.**

Every smoothly embedded two-sphere which bounds a convex body has at least two distinct
umbilic points. Alpöge's smooth support function has exactly one umbilic, so the answer is
false. -/
@[category research solved, AMS 52 53,
  formal_proof using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/7aa855bb344450777d9b19fe1cf11f2f5f9fae09/FormalConjectures/Other/CaratheodoryLoewnerCounterexample.lean#L75"]
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
