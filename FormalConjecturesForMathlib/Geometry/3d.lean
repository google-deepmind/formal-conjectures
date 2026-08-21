/-
Copyright 2025 The Formal Conjectures Authors.

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
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Orientation

/-!
# Three-dimensional Euclidean geometry

This file supplies the preferred orientation on `ℝ³` and transports the usual cross product on
coordinate triples to a bundled bilinear map on Euclidean space. It also records the standard
algebraic and metric identities for this cross product.
-/

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped EuclideanGeometry
open Matrix

/-- The standard basis gives us a preferred orientation in `ℝ³`.

Note: when upstreaming this to Mathlib (and generalizing to `Fin n`) one
must be careful to avoid an instance diamond with `IsEmpty.Orientation`.
Presumably this can be avoided by assuming `[NeZero n]`. -/
noncomputable instance Module.orientedEuclideanSpaceFinThree : Module.Oriented ℝ ℝ³ (Fin 3) :=
  ⟨Basis.orientation <| PiLp.basisFun ..⟩

/-- Three dimensional euclidean space is three-dimensional. -/
instance fact_finrank_euclideanSpace_fin_three : Fact (Module.finrank ℝ ℝ³ = 3) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace EuclideanHypersurface

/-- The usual cross product on three-dimensional Euclidean space, as a bundled bilinear map. -/
noncomputable def euclideanCross : ℝ³ →ₗ[ℝ] ℝ³ →ₗ[ℝ] ℝ³ :=
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  ((crossProduct.comp e.toLinearMap).compl₂ e.toLinearMap).compr₂ e.symm.toLinearMap

/-- The bundled Euclidean cross product agrees with the coordinate cross product. -/
theorem euclideanCross_apply (a b : ℝ³) :
    euclideanCross a b =
      WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) :=
  rfl

/-- Swapping the arguments of the cross product negates it. -/
@[simp]
theorem euclideanCross_anticomm (a b : ℝ³) :
    -euclideanCross a b = euclideanCross b a := by
  simpa only [euclideanCross_apply, map_neg] using
    congrArg (WithLp.toLp 2) (cross_anticomm (WithLp.ofLp a) (WithLp.ofLp b))

/-- A vector has zero cross product with itself. -/
@[simp]
theorem euclideanCross_self (a : ℝ³) : euclideanCross a a = 0 := by
  simpa only [euclideanCross_apply, map_zero] using
    congrArg (WithLp.toLp 2) (cross_self (WithLp.ofLp a))

/-- The cross product is orthogonal to its left input, with the inner-product arguments swapped. -/
@[simp]
theorem euclideanCross_inner_left (a b : ℝ³) : inner ℝ (euclideanCross a b) a = 0 := by
  rw [euclideanCross_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dot_self_cross]

/-- The cross product is orthogonal to its right input, with the inner-product arguments swapped. -/
@[simp]
theorem euclideanCross_inner_right (a b : ℝ³) : inner ℝ (euclideanCross a b) b = 0 := by
  rw [euclideanCross_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dot_cross_self]

/-- The inner product of two cross products is the corresponding Gram-determinant expression. -/
theorem inner_euclideanCross_euclideanCross (a b c d : ℝ³) :
    inner ℝ (euclideanCross a b) (euclideanCross c d) =
      inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp only [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    cross_dot_cross]
  rw [dotProduct_comm (WithLp.ofLp d) (WithLp.ofLp a)]
  ring

/-- The right-nested vector triple-product identity. -/
theorem euclideanCross_cross (u v w : ℝ³) :
    euclideanCross u (euclideanCross v w) =
      inner ℝ u w • v - inner ℝ u v • w := by
  change WithLp.toLp 2
    (crossProduct (WithLp.ofLp u) (crossProduct (WithLp.ofLp v) (WithLp.ofLp w))) = _
  rw [cross_cross_eq_smul_sub_smul']
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (WithLp.ofLp w) (WithLp.ofLp u),
    dotProduct_comm (WithLp.ofLp v) (WithLp.ofLp u)]
  rfl

/-- A cross product is nonzero exactly when its two inputs are linearly independent. -/
theorem euclideanCross_ne_zero_iff_linearIndependent (a b : ℝ³) :
    euclideanCross a b ≠ 0 ↔ LinearIndependent ℝ ![a, b] := by
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hne : euclideanCross a b ≠ 0 ↔ crossProduct (e a) (e b) ≠ 0 := by
    rw [euclideanCross]
    exact e.symm.injective.ne_iff
  rw [hne, crossProduct_ne_zero_iff_linearIndependent]
  have hLI := e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn
    (v := ![a, b])
  have hf : e.toLinearMap ∘ ![a, b] = ![e a, e b] := by
    funext i
    fin_cases i <;> simp
  rwa [hf] at hLI

/-- The cross product of two vectors orthogonal to a unit vector is parallel to that vector. -/
theorem euclideanCross_eq_inner_smul_of_orthogonal
    (p x y : ℝ³) (hp : ‖p‖ = 1) (hx : inner ℝ p x = 0) (hy : inner ℝ p y = 0) :
    euclideanCross x y = inner ℝ (euclideanCross x y) p • p := by
  let c := euclideanCross x y
  have hpc : euclideanCross p c = 0 := by
    dsimp only [c]
    rw [euclideanCross_cross, hy, hx]
    simp
  have hpp : inner ℝ p p = 1 := by
    simp [hp]
  have hsecond := euclideanCross_cross p p c
  rw [hpc, map_zero, hpp, one_smul] at hsecond
  have hc := (sub_eq_zero.mp hsecond.symm).symm
  simpa only [c, real_inner_comm] using hc

end EuclideanHypersurface
