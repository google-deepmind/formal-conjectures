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

import FormalConjectures.Other.LoewnerConjecture

/-!
# Carathéodory's conjecture

Carathéodory's conjecture says that every sufficiently smooth closed convex surface in
three-dimensional Euclidean space has at least two umbilic points. We state the conjecture for
smooth surfaces and the classical positive result for real-analytic surfaces. We also record
that Loewner's local index conjecture implies Carathéodory's global conjecture.

*References:*
- [M. Ghomi, *Open Problems in Geometry of Curves and Surfaces*, Problems 8.1 and
  8.2](https://ghomi.math.gatech.edu/Papers/op.pdf)
- [C. J. Titus, *A proof of a conjecture of Loewner and of the conjecture of Carathéodory on
  umbilic points*](https://doi.org/10.1007/BF02392036)
-/

open Set Metric
open scoped ContDiff EuclideanGeometry Manifold

namespace CaratheodoryConjecture

/-- A parametrized convex surface of class `C^k`, together with a `C^k` choice of unit normal.

The range condition says that the parametrization is the boundary of a convex body. Requiring
nonempty interior rules out lower-dimensional convex sets. -/
def IsConvexSphereOfClass (k : WithTop ℕ∞) (F n : sphere (0 : ℝ³) 1 → ℝ³) : Prop :=
  Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, ℝ³) k F ∧
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) k n ∧
    (∀ p, ‖n p‖ = 1) ∧
    (∀ p v, inner ℝ (n p) (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p v) = 0) ∧
    ∃ K : Set ℝ³,
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ range F = frontier K

/-- A smooth parametrized convex surface with a smooth choice of unit normal. -/
abbrev IsSmoothConvexSphere := IsConvexSphereOfClass ∞

/-- A real-analytic parametrized convex surface with a real-analytic choice of unit normal. -/
abbrev IsAnalyticConvexSphere := IsConvexSphereOfClass ω

/-- A point is umbilic when the derivative of the unit normal is a scalar multiple of the
derivative of the immersion, equivalently when its shape operator is scalar. -/
def IsUmbilic (F n : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) : Prop :=
  ∃ c : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) n p = c • mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p

/-- Carathéodory's conjecture for convex surfaces of class `C^k`. -/
def CaratheodoryConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ (F n : sphere (0 : ℝ³) 1 → ℝ³), IsConvexSphereOfClass k F n →
    ∃ p₁ p₂, p₁ ≠ p₂ ∧ IsUmbilic F n p₁ ∧ IsUmbilic F n p₂

/-- The smooth Carathéodory conjecture. -/
abbrev SmoothCaratheodoryConjecture := CaratheodoryConjectureOfClass ∞

/-- The real-analytic Carathéodory conjecture. -/
abbrev AnalyticCaratheodoryConjecture := CaratheodoryConjectureOfClass ω

/-- **The smooth Carathéodory conjecture.**

Every smoothly embedded two-sphere which bounds a convex body has at least two distinct
umbilic points. -/
@[category research open, AMS 52 53]
theorem caratheodory_conjecture : answer(sorry) ↔ SmoothCaratheodoryConjecture := by
  sorry

/-- **The real-analytic Carathéodory conjecture.**

Every real-analytically embedded two-sphere which bounds a convex body has at least two distinct
umbilic points. This is the classical theorem of Hamburger. -/
@[category research solved, AMS 52 53]
theorem caratheodory_conjecture_analytic : AnalyticCaratheodoryConjecture := by
  sorry

/-- The smooth Loewner conjecture implies the smooth Carathéodory conjecture by the
Poincaré–Hopf index theorem for principal line fields. -/
@[category research solved, AMS 52 53 57]
theorem loewner_implies_caratheodory :
    LoewnerConjecture.SmoothLoewnerConjecture → SmoothCaratheodoryConjecture := by
  sorry

end CaratheodoryConjecture
