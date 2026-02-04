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

import FormalConjectures.Util.ProblemImports

/-!
# Moving Sofa Problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Moving_sofa_problem)

[Ge92] Gerver, J. L., _On moving a sofa around a corner_. Geometriae Dedicata 42.3 (1992): 267-283.
[Ro18] Romik, D. _Differential equations and exact solutions in the moving sofa problem_. Experimental mathematics 27.3 (2018): 316-330.
[Ba24] Baek, J. _Optimality of Gerver's Sofa_. arXiv preprint arXiv:2411.19826 (2024).
-/

noncomputable section

/-- Interpret an affine isometry as a continuous affine map. This is already in Mathlib. -/
def _root_.AffineIsometry.toContinuousAffineMap {𝕜 V V₂ P P₂ : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
    [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P →ᵃⁱ[𝕜] P₂) : P →ᴬ[𝕜] P₂ := { f with cont := f.continuous }

namespace MovingSofa

open Topology
open scoped Real unitInterval

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

instance : Fact (Module.finrank ℝ ℝ² = 2) := ⟨finrank_euclideanSpace_fin⟩
instance : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩

/-- The **horizontal side** of the hallway is `(-∞, 1] × [0, 1]`. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is `[0, 1] × (-∞, 1]`. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set `s` is a **moving sofa** according to a rigid motion `m : I → SE(2)`,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since `SE(2)` is not in Mathlib yet, we use `E(2)` and rely on continuity and `m(0) = id` to
ensure `m` is in `SE(2)`.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/--
The rigid motion that translates by `p` and then rotates counterclockwise by `α`.
Note that [Ge92] used this definition while [Ro18] used rotation first and then translation.
-/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv
    |>.trans (AffineIsometryEquiv.vaddConst ℝ p)

/--
The sofa according to a rotation path `p : [0, π/2] → ℝ²` as in [Ge92] is the intersection over
`α ∈ [0, π/2]` of hallways each translated by `p(α)` and then rotated by `α`,
with the special cases that the hallway at `0` is the horizontal side
and the hallway at `π/2` is the vertical side.
-/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-!
Gerver's constants defining the sofa.

This section follows Theorem 2 of Gerver's paper [Ge92].
-/

/--
Eq. 1-4 of [Ro18], which specifies the constants `A`, `B`, `φ`, and `θ` of [Ge92].
-/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

@[category undergraduate, AMS 49]
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  sorry

def A : ℝ := ABφθSpec.existsUnique.choose.1
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

open MeasureTheory

/-- What is the maximal volume of a moving sofa? -/
@[category research open, AMS 49]
theorem iSup_isMovingSofa_volume :
    ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s = answer(sorry) :=
  sorry

/--
Gerver's sofa attains the maximal volume of a moving sofa, conjectured by [Ge92] and claimed by
[Ba24].
-/
@[category research open, AMS 49]
theorem maximalFor_isMovingSofa_volume_gerversSofa :
    MaximalFor (fun s ↦ ∃ m, IsMovingSofa s m) volume gerversSofa :=
  sorry

/-- Gerver's sofa attains the unique maximal volume of a moving sofa. -/
@[category research open, AMS 49]
theorem maximalFor_isMovingSofa_volume_iff_eq_gerversSofa :
    ∀ s : Set ℝ², MaximalFor (fun s ↦ ∃ m, IsMovingSofa s m) volume s ↔ s = gerversSofa :=
  sorry

end MovingSofa
