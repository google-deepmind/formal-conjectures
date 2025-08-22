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

import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import FormalConjectures.ForMathlib.Logic.Equiv.Fin.Rotate

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- Oriented angles make sense in 2d.

Note: this can't blindly be added to mathlib as it creates an "instance diamond"
with an instance for modules satisfying `is_empty`. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| Pi.basisFun _ _⟩

/-- Two dimensional euclidean space is two-dimensional. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

open scoped EuclideanGeometry

open scoped Real

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] {p : Fin n → P}

/-- The statement that a sequence of points form a counter-clockwise convex polygon. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (∡ (p i) (p j) (p k)).sign = 1

theorem IsCcwConvexPolygon.sign_oangle (hp : IsCcwConvexPolygon p) {i j k : Fin n}
  (hij : i < j) (hjk : j < k) : (∡ (p i) (p j) (p k)).sign = 1 := hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p j) (p k) (p i)).sign = 1 := by
  rw [EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle'' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p k) (p i) (p j)).sign = 1 := by
  rw [← EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

theorem IsCcwConvexPolygon.sign_oangle_finRotate (hp : IsCcwConvexPolygon p)
    (hn : 3 ≤ n) (i : Fin n) :
    (∡ (p i) (p <| finRotate _ i) (p <| finRotate _ (finRotate _ i))).sign = 1 := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp hn
  by_cases hi : i = Fin.last (n + 2)
  · rw [hi, finRotate_last, finRotate_apply_zero]
    exact hp.sign_oangle'' Fin.zero_lt_one Fin.one_lt_last
  by_cases hi' : finRotate _ i = Fin.last (n + 2)
  · rw [hi', finRotate_last]
    refine hp.sign_oangle' ?_ ((Fin.le_last _).lt_of_ne hi)
    rw [Fin.pos_iff_ne_zero]
    rintro rfl
    rw [finRotate_apply_zero] at hi'
    exact Fin.one_lt_last.ne hi'
  apply hp.sign_oangle <;> apply lt_finRotate_of_ne_last <;> assumption

@[simp] theorem isCcwConvexPolygon_zero (p : Fin 0 → P) : IsCcwConvexPolygon p := finZeroElim

@[simp] theorem isCcwConvexPolygon_one (p : Fin 1 → P) : IsCcwConvexPolygon p := by intro; omega

@[simp] theorem isCcwConvexPolygon_two (p : Fin 2 → P) : IsCcwConvexPolygon p := by intro; omega

set_option linter.docPrime false in
theorem isCcwConvexPolygon_four' {p : Fin 4 → P} :
    IsCcwConvexPolygon p ↔ (∡ (p 0) (p 1) (p 2)).sign = 1 ∧ (∡ (p 1) (p 2) (p 3)).sign = 1 ∧
    (∡ (p 2) (p 3) (p 0)).sign = 1 ∧ (∡ (p 3) (p 0) (p 1)).sign = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4⟩ ↦ ?_⟩
  · obtain ⟨h01, h12, h23⟩ : (0 : Fin 4) < 1 ∧ (1 : Fin 4) < 2 ∧ (2 : Fin 4) < 3 := by simp
    · repeat' constructor
      · exact h.sign_oangle h01 h12
      · exact h.sign_oangle h12 h23
      · exact h.sign_oangle' (h01.trans h12) h23
      · exact h.sign_oangle'' h01 (h12.trans h23)
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    · exact h1
    · rw [EuclideanGeometry.oangle_rotate_sign]
      exact h4
    · rw [← EuclideanGeometry.oangle_rotate_sign]
      exact h3
    · exact h2

@[simp]
theorem isCcwConvexPolygon_four (A B C D : P) :
    IsCcwConvexPolygon ![A, B, C, D] ↔
      (∡ A B C).sign = 1 ∧ (∡ B C D).sign = 1 ∧ (∡ C D A).sign = 1 ∧ (∡ D A B).sign = 1 :=
  isCcwConvexPolygon_four'

/-- The statement that a sequence of points form a convex polygon. -/
def IsConvexPolygon {n : ℕ} (p : Fin n → P) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i => p (-i)

/-- Three affine independent points always form a convex polygon. -/
theorem isConvexPolygon_three_of_affineIndependent {A B C : P}
    (hABC : AffineIndependent ℝ ![A, B, C]) : IsConvexPolygon ![A, B, C] := by
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff] at hABC
  cases hsABC : (∡ A B C).sign
  · exact (hABC hsABC).elim
  · right
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg, neg_eq_iff_eq_neg]
    exact (oangle_rotate_sign A B C).trans hsABC
  · left
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    exact hsABC

theorem isConvexPolygon_three_iff_affineIndependent {A B C : P} :
    IsConvexPolygon ![A, B, C] ↔ AffineIndependent ℝ ![A, B, C] := by
  refine ⟨fun h => ?_, isConvexPolygon_three_of_affineIndependent⟩
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff]
  let p := ![A, B, C]
  change IsConvexPolygon p at h
  change Real.Angle.sign (∡ (p 0) (p 1) (p 2)) ≠ 0
  cases' h with h h
  · rw [h.sign_oangle (by simp) (by simp)]
    rintro ⟨⟩
  · suffices Real.Angle.sign (∡ (p 0) (p 2) (p 1)) = 1 by rw [← oangle_swap₂₃_sign, this]; rintro ⟨⟩
    exact h.sign_oangle (i := 0) (j := 1) (k := 2) (by simp) (by simp)

theorem isConvexPolygon_triangle (t : Affine.Triangle ℝ P) : IsConvexPolygon t.points := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by ext i; fin_cases i <;> rfl
  rw [this, isConvexPolygon_three_iff_affineIndependent, ← this]
  exact t.independent

noncomputable def triangle_area (a b c : P) : ℝ :=
  positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2

lemma triangle_area_eq_det (a b c : ℝ²) :
    triangle_area a b c =
    Matrix.det !![a 0, b 0, c 0;
                  a 1, b 1, c 1;
                  1,   1,   1] / 2 := by
  rw [triangle_area, Orientation.areaForm_to_volumeForm,
    positiveOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl, Basis.det_apply]
  suffices (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1) =
      a 0 * b 1 - a 0 * c 1 - b 0 * a 1 + b 0 * c 1 + c 0 * a 1 - c 0 * b 1 by
    simp [Matrix.det_fin_two, Matrix.det_fin_three, Basis.toMatrix, this]
  ring

end EuclideanGeometry

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q
