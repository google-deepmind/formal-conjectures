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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic.Bound

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Projective analytification

This file supplies the compact topological model of finite-dimensional complex projective space.
It equips linear-algebraic projectivization with the quotient topology from nonzero coordinate
vectors. Normalizing coordinates gives a continuous surjection from the unit sphere, and hence
proves compactness.

It also constructs the standard scheme-theoretic projective points from homogeneous coordinates.
Standard affine charts prove that this construction is a continuous bijection from linear
projectivization onto the complex points of scheme-theoretic projective space. This proves that
scheme-theoretic projective space is analytically compact.
-/

@[expose] public section

open CategoryTheory Metric Opposite TopologicalSpace Topology
open scoped LinearAlgebra.Projectivization

namespace AlgebraicGeometry

namespace ComplexProjectiveSpace

/-- The coordinate vector space underlying complex projective `n`-space. -/
abbrev CoordinateSpace (n : ℕ) := Fin (n + 1) → ℂ

/-- The polynomial ring in homogeneous coordinates over the integral model. -/
abbrev UniversalRing (n : ℕ) := MvPolynomial (Fin (n + 1)) (ULift ℤ)

/-- The standard grading on the homogeneous coordinate ring. -/
abbrev UniversalGrading (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard quotient topology on finite-dimensional complex projective space. -/
noncomputable instance instTopologicalSpace (n : ℕ) :
    TopologicalSpace (Projectivization ℂ (CoordinateSpace n)) :=
  instTopologicalSpaceQuotient

/-- Normalize a nonzero vector to a vector on the unit sphere. -/
noncomputable def normalize {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    sphere (0 : CoordinateSpace n) 1 :=
  ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, by
    rw [mem_sphere, dist_zero_right, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)⟩

/-- A vector on the unit sphere is nonzero. -/
lemma sphere_ne_zero {n : ℕ} (v : sphere (0 : CoordinateSpace n) 1) :
    (v : CoordinateSpace n) ≠ 0 := by
  intro h
  simpa [h] using v.property

/-- The quotient map from the unit sphere to complex projective space. -/
noncomputable def sphereToProjectivization {n : ℕ} :
    sphere (0 : CoordinateSpace n) 1 → Projectivization ℂ (CoordinateSpace n) :=
  fun v ↦ Projectivization.mk ℂ v (sphere_ne_zero v)

/-- The quotient map from the unit sphere to complex projective space is continuous. -/
lemma continuous_sphereToProjectivization {n : ℕ} :
    Continuous (sphereToProjectivization (n := n)) := by
  change Continuous (Quotient.mk'' ∘
    (fun v : sphere (0 : CoordinateSpace n) 1 ↦
      (⟨(v : CoordinateSpace n), sphere_ne_zero v⟩ :
        {v : CoordinateSpace n // v ≠ 0})))
  exact continuous_quot_mk.comp (continuous_subtype_val.subtype_mk _)

/-- Every point of complex projective space has a unit-norm representative. -/
lemma surjective_sphereToProjectivization {n : ℕ} :
    Function.Surjective (sphereToProjectivization (n := n)) := by
  intro p
  induction p using Projectivization.ind with
  | _ v hv =>
      exact ⟨normalize v hv, (Projectivization.mk_eq_mk_iff' ℂ _ _ (sphere_ne_zero _) hv).2
        ⟨((‖v‖ : ℝ) : ℂ)⁻¹, rfl⟩⟩

/-- Finite-dimensional complex projective space is compact in its quotient topology. -/
noncomputable instance instCompactSpace (n : ℕ) :
    CompactSpace (Projectivization ℂ (CoordinateSpace n)) := by
  constructor
  rw [← (surjective_sphereToProjectivization (n := n)).range_eq]
  exact isCompact_range continuous_sphereToProjectivization

/-- A closed subset of finite-dimensional complex projective space is compact. -/
lemma isCompact_of_isClosed {n : ℕ}
    {Z : Set (Projectivization ℂ (CoordinateSpace n))} (hZ : IsClosed Z) :
    IsCompact Z :=
  hZ.isCompact

/-- Evaluation at a coordinate vector, regarded as a map to the global functions on
`Spec ℂ`. -/
noncomputable def coordinateGlobalSectionsHom {n : ℕ} (v : CoordinateSpace n) :
    UniversalRing n →+* ↑Γ(Spec ↧ℂ, ⊤) :=
  MvPolynomial.eval₂Hom
    ((algebraMap ℤ _).comp ULift.ringEquiv.toRingHom)
    ((Scheme.ΓSpecIso ↧ℂ).inv ∘ v)

@[simp]
lemma coordinateGlobalSectionsHom_X {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) :
    coordinateGlobalSectionsHom v (MvPolynomial.X i) =
      (Scheme.ΓSpecIso ↧ℂ).inv (v i) := by
  simp [coordinateGlobalSectionsHom]

/-- Evaluation of a homogeneous polynomial on scaled coordinates changes by the corresponding
power of the scale. -/
lemma eval₂_smul_of_isHomogeneous {n d : ℕ}
    (r : UniversalRing n) (hr : r.IsHomogeneous d)
    (c : ℂ) (v : CoordinateSpace n) :
    MvPolynomial.eval₂ ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) (c • v) r =
      c ^ d * MvPolynomial.eval₂
        ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) v r := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : ∑ i, m i = d := by
    rw [← hr (MvPolynomial.mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact (Finsupp.sum_fintype m (fun _ x ↦ x) (fun _ ↦ rfl)).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [show (∏ x, c ^ m x) = c ^ ∑ x, m x by
    simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin (n + 1))) m c]
  rw [hd]
  ring

/-- After identifying the global functions on `Spec ℂ` with `ℂ`, scaling coordinates
scales the value of a homogeneous polynomial by its degree. -/
lemma coordinateGlobalSectionsHom_smul {n d : ℕ}
    (r : UniversalRing n) (hr : r.IsHomogeneous d)
    (c : ℂ) (v : CoordinateSpace n) :
    (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom (c • v) r) =
      c ^ d * (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) := by
  have hEval (w : CoordinateSpace n) :
      (Scheme.ΓSpecIso ↧ℂ).hom.hom.comp (coordinateGlobalSectionsHom w) =
        MvPolynomial.eval₂Hom
          ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) w := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [coordinateGlobalSectionsHom]
    · intro j
      simp [coordinateGlobalSectionsHom]
  change ((Scheme.ΓSpecIso ↧ℂ).hom.hom.comp
      (coordinateGlobalSectionsHom (c • v))) r = c ^ d *
        ((Scheme.ΓSpecIso ↧ℂ).hom.hom.comp
          (coordinateGlobalSectionsHom v)) r
  rw [hEval, hEval]
  exact eval₂_smul_of_isHomogeneous r hr c v

/-- Evaluation of the integral homogeneous coordinate ring at a complex vector, with the global
functions on `Spec ℂ` identified with `ℂ`. -/
noncomputable def coordinateEvaluationHom {n : ℕ} (v : CoordinateSpace n) :
    UniversalRing n →+* ℂ :=
  (Scheme.ΓSpecIso ↧ℂ).hom.hom.comp (coordinateGlobalSectionsHom v)

@[simp]
lemma coordinateEvaluationHom_apply {n : ℕ} (v : CoordinateSpace n)
    (r : UniversalRing n) :
    coordinateEvaluationHom v r =
      (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) :=
  rfl

@[simp]
lemma coordinateEvaluationHom_X {n : ℕ} (v : CoordinateSpace n) (i : Fin (n + 1)) :
    coordinateEvaluationHom v (MvPolynomial.X i) = v i := by
  simp [coordinateEvaluationHom, coordinateGlobalSectionsHom_X]

/-- Evaluation of regular functions on the standard projective chart where the `i`-th coordinate
is nonzero. -/
noncomputable def awayCoordinateEvaluation {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+* ℂ :=
  (IsLocalization.Away.lift
    (S := Localization.Away (MvPolynomial.X i : UniversalRing n))
    (MvPolynomial.X i)
    (show IsUnit (coordinateEvaluationHom v (MvPolynomial.X i)) by
      rw [coordinateEvaluationHom_X]
      exact isUnit_iff_ne_zero.mpr hi)).comp
      (algebraMap
        (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i)))

/-- On the standard chart, a homogeneous fraction evaluates as its numerator divided by the
corresponding power of the nonzero coordinate. -/
lemma awayCoordinateEvaluation_mk {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) (d : ℕ)
    (r : UniversalRing n) (hr : r ∈ UniversalGrading n d) :
    awayCoordinateEvaluation v i hi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) d r (by simpa using hr)) =
      coordinateEvaluationHom v r * (v i) ⁻¹ ^ d := by
  simp only [awayCoordinateEvaluation, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift (coordinateEvaluationHom v) (MvPolynomial.X i) _)
      (Localization.mk r ⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (coordinateEvaluationHom v) (MvPolynomial.X i)
    r (v i) ⁻¹]
  rw [coordinateEvaluationHom_X]
  exact mul_inv_cancel₀ hi

/-- Degree-zero localized coordinate evaluation is unchanged when all homogeneous coordinates are
rescaled by the same nonzero scalar. -/
lemma awayCoordinateEvaluation_smul {n : ℕ} (v : CoordinateSpace n)
    (c : ℂ) (hc : c ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    awayCoordinateEvaluation (c • v) i (mul_ne_zero hc hi) =
      awayCoordinateEvaluation v i hi := by
  ext z
  obtain ⟨d, r, hr, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (UniversalGrading n) (MvPolynomial.isHomogeneous_X (ULift ℤ) i) z
  have hr' : r ∈ UniversalGrading n d := by simpa using hr
  rw [awayCoordinateEvaluation_mk (hr := hr'), awayCoordinateEvaluation_mk (hr := hr')]
  rw [coordinateEvaluationHom_apply, coordinateEvaluationHom_apply,
    coordinateGlobalSectionsHom_smul r hr' c v]
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_pow]
  calc
    _ = ((Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) *
        (v i)⁻¹ ^ d) *
        (c ^ d * c⁻¹ ^ d) := by ring
    _ = ((Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) *
        (v i)⁻¹ ^ d) *
        (c * c⁻¹) ^ d := by rw [mul_pow]
    _ = _ := by rw [mul_inv_cancel₀ hc, one_pow, mul_one]

/-- Evaluation on the degree-zero localization away from an arbitrary homogeneous polynomial. -/
noncomputable def awayHomogeneousEvaluation {n d : ℕ} (v : CoordinateSpace n)
    (f : UniversalRing n) (_hf : f ∈ UniversalGrading n d)
    (hv : coordinateEvaluationHom v f ≠ 0) :
    HomogeneousLocalization.Away (UniversalGrading n) f →+* ℂ :=
  (IsLocalization.Away.lift
    (S := Localization.Away f) f
    (show IsUnit (coordinateEvaluationHom v f) from isUnit_iff_ne_zero.mpr hv)).comp
      (algebraMap
        (HomogeneousLocalization.Away (UniversalGrading n) f)
        (Localization.Away f))

/-- Evaluation on a homogeneous fraction is evaluation of its numerator divided by evaluation of
the denominator to the same power. -/
lemma awayHomogeneousEvaluation_mk {n d : ℕ} (v : CoordinateSpace n)
    (f : UniversalRing n) (hf : f ∈ UniversalGrading n d)
    (hv : coordinateEvaluationHom v f ≠ 0) (k : ℕ)
    (r : UniversalRing n) (hr : r ∈ UniversalGrading n (k * d)) :
    awayHomogeneousEvaluation v f hf hv
      (HomogeneousLocalization.Away.mk (UniversalGrading n) hf k r
        (by simpa [nsmul_eq_mul] using hr)) =
      coordinateEvaluationHom v r * (coordinateEvaluationHom v f)⁻¹ ^ k := by
  simp only [awayHomogeneousEvaluation, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift (coordinateEvaluationHom v) f _)
      (Localization.mk r ⟨f ^ k, ⟨k, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (coordinateEvaluationHom v) f
    r (coordinateEvaluationHom v f)⁻¹]
  exact mul_inv_cancel₀ hv

/-- The regular function `X_j / X_i` on the standard projective chart where `X_i` is
nonzero. -/
noncomputable def chartCoordinate {n : ℕ} (i j : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk (UniversalGrading n)
    (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j)
      (by simpa using MvPolynomial.isHomogeneous_X (ULift ℤ) j)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma chartCoordinate_self {n : ℕ} (i : Fin (n + 1)) :
    chartCoordinate (n := n) i i = 1 := by
  rw [HomogeneousLocalization.ext_iff_val]
  unfold chartCoordinate
  rw [HomogeneousLocalization.Away.val_mk]
  simp

/-- The homogeneous coordinate variables generate the polynomial ring over its degree-zero
subring. -/
lemma adjoin_coordinates_eq_top (n : ℕ) :
    Algebra.adjoin (UniversalGrading n 0)
      (Set.range (MvPolynomial.X : Fin (n + 1) → UniversalRing n)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact (Algebra.adjoin (UniversalGrading n 0)
        (Set.range (MvPolynomial.X : Fin (n + 1) → UniversalRing n))).algebraMap_mem
          ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ _⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

set_option backward.isDefEq.respectTransparency.types false in
lemma chartGenerator_eq_prod {n a : ℕ} (i : Fin (n + 1))
    (ai : Fin (n + 1) → ℕ) (hai : ∑ j, ai j = a) :
    HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) a
        (∏ j, MvPolynomial.X j ^ ai j)
        (by
          convert SetLike.prod_pow_mem_graded (UniversalGrading n) (fun _ ↦ (1 : ℕ))
            (fun j ↦ MvPolynomial.X j) ai (F := Finset.univ)
              (fun j _ ↦ MvPolynomial.isHomogeneous_X (ULift ℤ) j) using 1;
            simp [hai]) =
      ∏ j, chartCoordinate i j ^ ai j := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    show (∏ j, chartCoordinate i j ^ ai j).val =
      ∏ j, (chartCoordinate i j).val ^ ai j by
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction with
    | empty => exact HomogeneousLocalization.val_one
    | @insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.prod_insert hjs,
          HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, ih]]
  simp only [chartCoordinate, HomogeneousLocalization.Away.val_mk]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod (Finset.univ : Finset (Fin (n + 1)))]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow,
    one_mul]
  congr 1
  simp [Finset.prod_pow_eq_pow_sum, hai]

set_option linter.style.haveILetI false in
/-- A ring map from a standard projective chart is determined by the coordinate ratios. -/
lemma awayRingHom_ext {n : ℕ} (i : Fin (n + 1))
    (φ ψ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ)
    (hbase : ∀ a : UniversalGrading n 0,
      φ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a) =
      ψ (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n)) a))
    (hcoord : ∀ j, φ (chartCoordinate i j) = ψ (chartCoordinate i j)) :
    φ = ψ := by
  letI : Algebra (UniversalGrading n 0) ℂ :=
    (φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n)))).toAlgebra
  let φa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] ℂ :=
    { φ with commutes' := fun _ ↦ rfl }
  let ψa : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →ₐ[UniversalGrading n 0] ℂ :=
    { ψ with commutes' := fun r ↦ (hbase r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (Fin (n + 1)) (fun j ↦ MvPolynomial.X j) (adjoin_coordinates_eq_top n)
      (fun _ ↦ (1 : ℕ)) (fun j ↦ MvPolynomial.isHomogeneous_X (ULift ℤ) j))
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  change φ (chartCoordinate i j ^ ai j) = ψ (chartCoordinate i j ^ ai j)
  rw [φ.map_pow, ψ.map_pow, hcoord]

/-- The degree-zero coefficient ring of the standard projective grading has a unique ring map to
`ℂ`. -/
lemma degreeZero_ringHom_unique {n : ℕ}
    (φ ψ : UniversalGrading n 0 →+* ℂ) : φ = ψ := by
  ext a
  obtain ⟨z, rfl⟩ :=
    (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift ℤ)).symm.surjective a
  obtain ⟨z, rfl⟩ := (ULift.ringEquiv (R := ℤ)).symm.surjective z
  exact DFunLike.congr_fun (Subsingleton.elim
    ((φ.comp (ProjectiveSpace.degreeZeroEquiv
      (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
    ((ψ.comp (ProjectiveSpace.degreeZeroEquiv
      (Fin (n + 1)) (ULift ℤ)).symm.toRingHom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)) z

/-- Homogeneous coordinates reconstructed from a complex point of one standard affine chart. -/
noncomputable def vectorOfAwayRingHom {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ) : CoordinateSpace n :=
  fun j ↦ φ (chartCoordinate i j)

@[simp]
lemma vectorOfAwayRingHom_apply {n : ℕ} (i j : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ) :
    vectorOfAwayRingHom i φ j = φ (chartCoordinate i j) :=
  rfl

@[simp]
lemma vectorOfAwayRingHom_self {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ) :
    vectorOfAwayRingHom i φ i = 1 := by
  rw [vectorOfAwayRingHom_apply, chartCoordinate_self, map_one]

lemma vectorOfAwayRingHom_ne_zero {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ) :
    vectorOfAwayRingHom i φ ≠ 0 := by
  intro h
  have hi := vectorOfAwayRingHom_self i φ
  rw [h] at hi
  exact one_ne_zero hi.symm

/-- Reconstructing coordinates from a chart ring map and evaluating them recovers that ring map. -/
lemma awayCoordinateEvaluation_vectorOfAwayRingHom {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* ℂ) :
    awayCoordinateEvaluation (vectorOfAwayRingHom i φ) i
      (by
        rw [vectorOfAwayRingHom_self]
        exact one_ne_zero) = φ := by
  let v := vectorOfAwayRingHom i φ
  have hi : v i ≠ 0 := by
    change vectorOfAwayRingHom i φ i ≠ 0
    rw [vectorOfAwayRingHom_self]
    exact one_ne_zero
  change awayCoordinateEvaluation v i hi = φ
  apply awayRingHom_ext i
  · intro a
    exact DFunLike.congr_fun (degreeZero_ringHom_unique
      ((awayCoordinateEvaluation v i hi).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))
      (φ.comp (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
        (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))) a
  · intro j
    change awayCoordinateEvaluation v i hi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) =
      φ (chartCoordinate i j)
    rw [awayCoordinateEvaluation_mk (d := 1) (r := MvPolynomial.X j)
      (hr := by simpa using MvPolynomial.isHomogeneous_X (ULift ℤ) j)]
    simp only [coordinateEvaluationHom_X, one_pow, v, vectorOfAwayRingHom_apply,
      chartCoordinate_self, map_one, inv_one, mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation on the overlap `D₊(X_i X_j)`, restricted to `D₊(X_i)`, is evaluation in the
`i`-th standard chart. -/
lemma awayHomogeneousEvaluation_comp_awayMap_coordinate {n : ℕ}
    (v : CoordinateSpace n) (i j : Fin (n + 1))
    (hi : v i ≠ 0) (hj : v j ≠ 0) :
    (awayHomogeneousEvaluation (d := 2) v (MvPolynomial.X i * MvPolynomial.X j)
      (by simpa using (SetLike.mul_mem_graded (A := UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) j)))
      (by simp [hi, hj])).comp
        (HomogeneousLocalization.awayMap (UniversalGrading n)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) j) rfl) =
      awayCoordinateEvaluation v i hi := by
  let hfij : MvPolynomial.X i * MvPolynomial.X j ∈ UniversalGrading n 2 := by
    convert SetLike.mul_mem_graded (A := UniversalGrading n)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) j) using 1
  let hvij : coordinateEvaluationHom v (MvPolynomial.X i * MvPolynomial.X j) ≠ 0 := by
    simp [hi, hj]
  let φij := awayHomogeneousEvaluation v (MvPolynomial.X i * MvPolynomial.X j) hfij hvij
  change φij.comp
      (HomogeneousLocalization.awayMap (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) j) rfl) =
    awayCoordinateEvaluation v i hi
  apply awayRingHom_ext i
  · intro a
    exact DFunLike.congr_fun (degreeZero_ringHom_unique
      ((φij.comp
        (HomogeneousLocalization.awayMap (UniversalGrading n)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) j) rfl)).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))
      ((awayCoordinateEvaluation v i hi).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))) a
  · intro k
    change φij
      (HomogeneousLocalization.awayMap (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) j) rfl (chartCoordinate i k)) =
      awayCoordinateEvaluation v i hi (chartCoordinate i k)
    unfold chartCoordinate
    rw [HomogeneousLocalization.awayMap_mk, awayHomogeneousEvaluation_mk (k := 1)
      (hr := by simpa using (SetLike.mul_mem_graded (A := UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) k)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) j))),
      awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) k)]
    simp only [map_mul, coordinateEvaluationHom_X]
    field_simp
    simp

/-- A nonzero coordinate vector has a nonzero coordinate. -/
lemma exists_coordinate_ne_zero {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 := by
  contrapose! hv
  exact funext hv

/-- The finite set of indices of the nonzero coordinates of a vector. -/
noncomputable def coordinateSupport {n : ℕ} (v : CoordinateSpace n) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i ↦ v i ≠ 0)

lemma coordinateSupport_nonempty {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    (coordinateSupport v).Nonempty := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  exact ⟨i, by simp [coordinateSupport, hi]⟩

/-- The least index of a nonzero coordinate. This gives a scale-independent choice of a
standard projective chart. -/
noncomputable def coordinateIndex {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Fin (n + 1) :=
  (coordinateSupport v).min' (coordinateSupport_nonempty v hv)

lemma coordinateIndex_ne_zero {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    v (coordinateIndex v hv) ≠ 0 := by
  classical
  simpa [coordinateIndex, coordinateSupport] using
    (coordinateSupport v).min'_mem (coordinateSupport_nonempty v hv)

/-- Rescaling by a nonzero scalar does not change the selected standard chart. -/
lemma coordinateIndex_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    coordinateIndex (c • v) (smul_ne_zero hc hv) = coordinateIndex v hv := by
  classical
  have hs : coordinateSupport (c • v) = coordinateSupport v := by
    ext i
    simp [coordinateSupport, hc]
  unfold coordinateIndex
  congr

/-- The projective point defined directly in one standard affine chart. -/
noncomputable def chartIntegralProjAt {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    Spec ↧ℂ ⟶ Proj (UniversalGrading n) :=
  Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)) ≫
    Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one

set_option linter.style.haveILetI false in
/-- Every complex point whose image lies in a standard projective chart is obtained by evaluating
homogeneous coordinates. -/
lemma exists_coordinates_of_range_subset_chart {n : ℕ}
    (q : Spec ↧ℂ ⟶ Proj (UniversalGrading n)) (i : Fin (n + 1))
    (hq : Set.range q ⊆ Set.range
      (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)) :
    ∃ (v : CoordinateSpace n) (_hv : v ≠ 0) (hi : v i ≠ 0),
      chartIntegralProjAt v i hi = q := by
  let e := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  letI : IsOpenImmersion e := by
    dsimp [e]
    exact Proj.instIsOpenImmersionAwayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  let l : Spec ↧ℂ ⟶
      Spec ↧(HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)) :=
    IsOpenImmersion.lift e q hq
  let φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i) →+* ℂ := (Spec.preimage l).hom
  let v := vectorOfAwayRingHom i φ
  have hv : v ≠ 0 := vectorOfAwayRingHom_ne_zero i φ
  have hi : v i ≠ 0 := (vectorOfAwayRingHom_self i φ).trans_ne one_ne_zero
  refine ⟨v, hv, hi, ?_⟩
  unfold chartIntegralProjAt
  rw [awayCoordinateEvaluation_vectorOfAwayRingHom]
  change Spec.map (Spec.preimage l) ≫ e = q
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac e q hq

lemma chartIntegralProjAt_congr {n : ℕ} (v : CoordinateSpace n)
    {i j : Fin (n + 1)} (hi : v i ≠ 0) (hj : v j ≠ 0) (hij : i = j) :
    chartIntegralProjAt v i hi = chartIntegralProjAt v j hj := by
  subst hij
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The projective morphism defined by a coordinate vector is independent of the chosen nonzero
standard coordinate. -/
lemma chartIntegralProjAt_independent {n : ℕ} (v : CoordinateSpace n)
    (i j : Fin (n + 1)) (hi : v i ≠ 0) (hj : v j ≠ 0) :
    chartIntegralProjAt v i hi = chartIntegralProjAt v j hj := by
  let φij := awayHomogeneousEvaluation (d := 2) v
    (MvPolynomial.X i * MvPolynomial.X j)
    (by simpa using (SetLike.mul_mem_graded (A := UniversalGrading n)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) j)))
    (by simp [hi, hj])
  have hfi : φij.comp
        (HomogeneousLocalization.awayMap (UniversalGrading n)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) j) rfl) =
      awayCoordinateEvaluation v i hi :=
    awayHomogeneousEvaluation_comp_awayMap_coordinate v i j hi hj
  have hfj : φij.comp
        (HomogeneousLocalization.awayMap (UniversalGrading n)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) (mul_comm _ _)) =
      awayCoordinateEvaluation v j hj := by
    apply awayRingHom_ext j
    · intro a
      exact DFunLike.congr_fun (degreeZero_ringHom_unique
        ((φij.comp
          (HomogeneousLocalization.awayMap (UniversalGrading n)
            (MvPolynomial.isHomogeneous_X (ULift ℤ) i) (mul_comm _ _))).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
            (Submonoid.powers (MvPolynomial.X j : UniversalRing n))))
        ((awayCoordinateEvaluation v j hj).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
            (Submonoid.powers (MvPolynomial.X j : UniversalRing n))))) a
    · intro k
      change φij
        (HomogeneousLocalization.awayMap (UniversalGrading n)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) (mul_comm _ _)
            (chartCoordinate j k)) =
        awayCoordinateEvaluation v j hj (chartCoordinate j k)
      unfold chartCoordinate
      rw [HomogeneousLocalization.awayMap_mk, awayHomogeneousEvaluation_mk (k := 1)
        (hr := by simpa [mul_comm] using
          (SetLike.mul_mem_graded (A := UniversalGrading n)
            (MvPolynomial.isHomogeneous_X (ULift ℤ) k)
            (MvPolynomial.isHomogeneous_X (ULift ℤ) i))),
        awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) k)]
      simp only [map_mul, coordinateEvaluationHom_X]
      field_simp
      simp
  unfold chartIntegralProjAt
  rw [← hfi, ← hfj]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

set_option backward.isDefEq.respectTransparency.types false in
/-- A coordinate point lies in the `i`-th standard open exactly when its `i`-th coordinate is
nonzero. -/
lemma chartIntegralProjAt_preimage_coordinateBasicOpen {n : ℕ}
    (v : CoordinateSpace n) (k : Fin (n + 1)) (hk : v k ≠ 0)
    (i : Fin (n + 1)) :
    chartIntegralProjAt v k hk ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) =
        if v i = 0 then ⊥ else ⊤ := by
  unfold chartIntegralProjAt
  rw [Scheme.Hom.comp_preimage, show Proj.awayι (UniversalGrading n) (MvPolynomial.X k)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) k) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) k)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i)) from
    Proj.awayι_preimage_basicOpen
      (𝒜 := UniversalGrading n) (f := MvPolynomial.X k) (g := MvPolynomial.X i)
      (m := 1) (m' := 1)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) k) zero_lt_one
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one]
  rw [SpecMap_preimage_basicOpen, show HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) k)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) = chartCoordinate k i by
    rw [HomogeneousLocalization.ext_iff_val]
    unfold chartCoordinate HomogeneousLocalization.Away.isLocalizationElem
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
    simp]
  unfold chartCoordinate
  simp only [CommRingCat.hom_ofHom]
  rw [awayCoordinateEvaluation_mk
    (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) i)]
  simp only [coordinateEvaluationHom_X]
  split_ifs with hi
  · rw [hi, zero_mul, PrimeSpectrum.basicOpen_zero]
    rfl
  · apply top_unique
    intro x hx
    change v i * (v k)⁻¹ ^ 1 ∉ x.asIdeal
    rw [Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using mul_ne_zero hi (inv_ne_zero hk)

/-- Direct chart points are unchanged by rescaling their coordinates. -/
lemma chartIntegralProjAt_smul {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    chartIntegralProjAt (c • v) i (mul_ne_zero hc hi) = chartIntegralProjAt v i hi := by
  unfold chartIntegralProjAt
  rw [awayCoordinateEvaluation_smul v c hc i hi]

/-- The projective point obtained in the least standard chart containing it. -/
noncomputable def chartIntegralProj {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Spec ↧ℂ ⟶ Proj (UniversalGrading n) :=
  chartIntegralProjAt v (coordinateIndex v hv) (coordinateIndex_ne_zero v hv)

/-- The chosen-chart construction is unchanged by nonzero rescaling. -/
lemma chartIntegralProj_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    chartIntegralProj (c • v) (smul_ne_zero hc hv) = chartIntegralProj v hv := by
  let i := coordinateIndex v hv
  have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  have hci : (c • v) i ≠ 0 := by simpa using mul_ne_zero hc hi
  calc
    chartIntegralProj (c • v) (smul_ne_zero hc hv) =
        chartIntegralProjAt (c • v) i hci :=
      chartIntegralProjAt_congr _ _ _ (coordinateIndex_smul v hv c hc)
    _ = chartIntegralProjAt v i hi := chartIntegralProjAt_smul v i hi c hc
    _ = chartIntegralProj v hv := rfl

/-- The selected-chart construction agrees with evaluation in every nonzero coordinate chart. -/
lemma chartIntegralProj_eq_chartIntegralProjAt {n : ℕ} (v : CoordinateSpace n)
    (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    chartIntegralProj v hv = chartIntegralProjAt v i hi :=
  chartIntegralProjAt_independent v (coordinateIndex v hv) i
    (coordinateIndex_ne_zero v hv) hi

/-- The irrelevant ideal of the homogeneous coordinate ring is contained in the ideal generated
by the degree-one coordinates. -/
lemma irrelevant_le_span_coordinates (n : ℕ) :
    (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → UniversalRing n)) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro r hr
  simp only [Set.mem_iUnion] at hr
  obtain ⟨d, hd⟩ := hr
  obtain ⟨hd0, hr⟩ := hd
  have hrpow : r ∈
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → UniversalRing n)) ^ d := by
    rw [Ideal.span_pow_eq_map_homogeneousSubmodule]
    exact ⟨MvPolynomial.map MvPolynomial.C r, hr.map _, by simp⟩
  exact Ideal.pow_le_self hd0.ne' hrpow

/-- The standard coordinate basic opens cover the integral `Proj` model of finite-dimensional
projective space. -/
lemma iSup_coordinateBasicOpen_eq_top (n : ℕ) :
    ⨆ i : Fin (n + 1),
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (irrelevant_le_span_coordinates n)

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
/-- Every complex point of the integral projective spectrum has homogeneous coordinates in some
standard affine chart. -/
lemma exists_coordinates_of_integralProj {n : ℕ}
    (q : Spec ↧ℂ ⟶ Proj (UniversalGrading n)) :
    ∃ (i : Fin (n + 1)) (v : CoordinateSpace n) (_hv : v ≠ 0) (hi : v i ≠ 0),
      chartIntegralProjAt v i hi = q := by
  have hmem : q (IsLocalRing.closedPoint ℂ) ∈ (⊤ : (Proj (UniversalGrading n)).Opens) :=
    trivial
  rw [← iSup_coordinateBasicOpen_eq_top n,
    TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi⟩ := hmem
  let e := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  letI : IsOpenImmersion e := by
    dsimp [e]
    exact Proj.instIsOpenImmersionAwayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  have hRange : Set.range q ⊆ Set.range e := by
    change Set.range q ⊆ e.opensRange
    dsimp only [e]
    rw [Proj.opensRange_awayι]
    rintro _ ⟨x, rfl⟩
    obtain rfl := Subsingleton.elim x (IsLocalRing.closedPoint ℂ)
    exact hi
  obtain ⟨v, hv, hvi, hq⟩ := exists_coordinates_of_range_subset_chart q i hRange
  exact ⟨i, v, hv, hvi, hq⟩

/-- Every complex-valued point of the integral projective spectrum is represented by a nonzero
homogeneous coordinate vector. -/
lemma surjective_chartIntegralProj {n : ℕ} :
    Function.Surjective (fun v : {v : CoordinateSpace n // v ≠ 0} ↦
      chartIntegralProj v.1 v.2) := by
  intro q
  obtain ⟨i, v, hv, hi, hq⟩ := exists_coordinates_of_integralProj q
  refine ⟨⟨v, hv⟩, ?_⟩
  change chartIntegralProj v hv = q
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi, hq]

set_option backward.isDefEq.respectTransparency.types false in
/-- Equal projective-spectrum morphisms constructed from nonzero vectors determine the same
linear projective point. -/
lemma projectivization_mk_eq_of_chartIntegralProj_eq {n : ℕ}
    (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : chartIntegralProj v hv = chartIntegralProj w hw) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  let i := coordinateIndex v hv
  have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  have hvopen : IsLocalRing.closedPoint ℂ ∈
      chartIntegralProj v hv ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
    rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
      chartIntegralProjAt_preimage_coordinateBasicOpen]
    simp [hi]
    exact trivial
  have hwopen : IsLocalRing.closedPoint ℂ ∈
      chartIntegralProj w hw ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
    rw [← h]
    exact hvopen
  have hwi : w i ≠ 0 := by
    intro hwi
    rw [chartIntegralProj_eq_chartIntegralProjAt w hw
        (coordinateIndex w hw) (coordinateIndex_ne_zero w hw),
      chartIntegralProjAt_preimage_coordinateBasicOpen, if_pos hwi] at hwopen
    exact hwopen
  have hcharts : chartIntegralProjAt v i hi = chartIntegralProjAt w i hwi := by
    rw [← chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
      ← chartIntegralProj_eq_chartIntegralProjAt w hw i hwi]
    exact h
  have hspec : Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)) =
      Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation w i hwi)) := by
    unfold chartIntegralProjAt at hcharts
    exact (cancel_mono
      (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)).mp hcharts
  have hcat : CommRingCat.ofHom (awayCoordinateEvaluation v i hi) =
      CommRingCat.ofHom (awayCoordinateEvaluation w i hwi) :=
    Spec.map_injective hspec
  have heval : awayCoordinateEvaluation v i hi = awayCoordinateEvaluation w i hwi :=
    congrArg ConcreteCategory.hom hcat
  apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).2
  refine ⟨v i * (w i)⁻¹, ?_⟩
  funext j
  have hj := DFunLike.congr_fun heval (chartCoordinate i j)
  change awayCoordinateEvaluation v i hi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) =
    awayCoordinateEvaluation w i hwi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) at hj
  rw [awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j),
    awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j)] at hj
  simp only [coordinateEvaluationHom_X] at hj
  change (v i * (w i)⁻¹) * w j = v j
  field_simp [hi, hwi] at hj ⊢
  exact hj.symm

/-- Nonzero homogeneous coordinates satisfy the irrelevant-ideal condition in the universal
construction of a morphism to `Proj`. -/
lemma coordinate_irrelevant_map_eq_top {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Ideal.map (coordinateGlobalSectionsHom v)
      (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal = ⊤ := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  apply Ideal.eq_top_of_isUnit_mem _
  · apply Ideal.mem_map_of_mem
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i)
  · rw [coordinateGlobalSectionsHom_X]
    exact IsUnit.map (Scheme.ΓSpecIso ↧ℂ).inv.hom
      (isUnit_iff_ne_zero.mpr hi)

/-- Nonzero homogeneous coordinates define a morphism from `Spec ℂ` to the integral `Proj`
model. -/
noncomputable def toIntegralProj {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Spec ↧ℂ ⟶ Proj (UniversalGrading n) :=
  Proj.fromOfGlobalSections (UniversalGrading n) (coordinateGlobalSectionsHom v)
    (coordinate_irrelevant_map_eq_top v hv)

/-- The inverse image of a positive-degree basic open under the point constructed from
coordinates is determined by whether the homogeneous polynomial vanishes at those coordinates. -/
lemma toIntegralProj_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    toIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) = 0
        then ⊥ else ⊤ := by
  rw [toIntegralProj,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd hr]
  rw [basicOpen_eq_of_affine']
  let a : ℂ := (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r)
  change PrimeSpectrum.basicOpen a = if a = 0 then ⊥ else ⊤
  split_ifs with h
  · rw [h]
    exact PrimeSpectrum.basicOpen_zero
  · apply top_unique
    intro x hx
    rw [PrimeSpectrum.mem_basicOpen, Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using h

/-- The coordinate chart met by the point constructed from a vector is exactly the chart on
which that coordinate is nonzero. -/
lemma toIntegralProj_preimage_coordinateBasicOpen {n : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0) (i : Fin (n + 1)) :
    toIntegralProj v hv ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) =
        if v i = 0 then ⊥ else ⊤ := by
  rw [toIntegralProj,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i)]
  rw [coordinateGlobalSectionsHom_X, basicOpen_eq_of_affine']
  let a : ℂ := (Scheme.ΓSpecIso ↧ℂ).hom
    ((Scheme.ΓSpecIso ↧ℂ).inv (v i))
  have ha : a = v i := Iso.hom_inv_id_apply _ _
  change PrimeSpectrum.basicOpen a = _
  rw [ha]
  split_ifs with h
  · rw [h]
    exact PrimeSpectrum.basicOpen_zero
  · apply top_unique
    intro x hx
    rw [PrimeSpectrum.mem_basicOpen, Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using h

/-- Rescaling nonzero homogeneous coordinates does not change the underlying point of the
integral `Proj` model. -/
lemma toIntegralProj_apply_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : Spec ↧ℂ) :
    toIntegralProj (c • v) (smul_ne_zero hc hv) x = toIntegralProj v hv x := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  apply ProjectiveSpectrum.ext
  ext r
  rw [(toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal.isHomogeneous.mem_iff,
    (toIntegralProj v hv x).asHomogeneousIdeal.isHomogeneous.mem_iff]
  apply forall_congr'
  intro d
  let s : UniversalRing n :=
    GradedRing.proj (UniversalGrading n) d r
  have hs : s ∈ UniversalGrading n d := SetLike.coe_mem _
  let t : UniversalRing n := s * MvPolynomial.X i
  have ht : t ∈ UniversalGrading n (d + 1) :=
    SetLike.mul_mem_graded hs (MvPolynomial.isHomogeneous_X _ i)
  have hXi_v : MvPolynomial.X i ∉
      (toIntegralProj v hv x).asHomogeneousIdeal := by
    rw [← Proj.mem_basicOpen]
    change x ∈ toIntegralProj v hv ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i)
    rw [toIntegralProj_preimage_basicOpen v hv (MvPolynomial.X i) zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i), coordinateGlobalSectionsHom_X]
    simp [hi]
  have hXi_cv : MvPolynomial.X i ∉
      (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal := by
    rw [← Proj.mem_basicOpen]
    change x ∈ toIntegralProj (c • v) (smul_ne_zero hc hv) ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i)
    rw [toIntegralProj_preimage_basicOpen (c • v) (smul_ne_zero hc hv)
      (MvPolynomial.X i) zero_lt_one (MvPolynomial.isHomogeneous_X _ i),
      coordinateGlobalSectionsHom_X]
    simp [hi, hc]
  have htmem (w : CoordinateSpace n) (hw : w ≠ 0) :
      t ∈ (toIntegralProj w hw x).asHomogeneousIdeal ↔
        (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom w t) = 0 := by
    rw [← not_iff_not, ← Proj.mem_basicOpen]
    change x ∈ toIntegralProj w hw ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) t ↔ _
    rw [toIntegralProj_preimage_basicOpen w hw t (Nat.zero_lt_succ d) ht]
    split_ifs with h <;> simp [h]
  change s ∈ (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal ↔
    s ∈ (toIntegralProj v hv x).asHomogeneousIdeal
  have hmul_cv : t ∈
      (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal ↔
        s ∈ (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal :=
    ⟨fun h ↦ ((toIntegralProj (c • v) (smul_ne_zero hc hv) x).isPrime.mem_or_mem
      h).resolve_right hXi_cv, fun h ↦ Ideal.mul_mem_right _ _ h⟩
  have hmul_v : t ∈ (toIntegralProj v hv x).asHomogeneousIdeal ↔
      s ∈ (toIntegralProj v hv x).asHomogeneousIdeal :=
    ⟨fun h ↦ ((toIntegralProj v hv x).isPrime.mem_or_mem h).resolve_right hXi_v,
      fun h ↦ Ideal.mul_mem_right _ _ h⟩
  rw [← hmul_cv, ← hmul_v, htmem, htmem, coordinateGlobalSectionsHom_smul t ht c v]
  simp [hc]

/-- Homogeneous coordinates give a scale-independent map to the underlying projective spectrum.
This is the point-level part of the comparison with scheme-theoretic projective space. -/
noncomputable def projectivizationToIntegralProjPointAt {n : ℕ} (x : Spec ↧ℂ) :
    Projectivization ℂ (CoordinateSpace n) → Proj (UniversalGrading n) :=
  Projectivization.lift
    (fun v ↦ toIntegralProj v.1 v.2 x)
    (fun a b c h ↦ by
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [h, hc, zero_smul]
      simpa only [h] using toIntegralProj_apply_smul b.1 b.2 c hc x)

@[simp]
lemma projectivizationToIntegralProjPointAt_mk {n : ℕ} (x : Spec ↧ℂ)
    (v : CoordinateSpace n) (hv : v ≠ 0) :
    projectivizationToIntegralProjPointAt x (Projectivization.mk ℂ v hv) =
      toIntegralProj v hv x :=
  rfl

/-- Nonzero homogeneous coordinates define a point of scheme-theoretic projective space over
`Spec ℂ`. -/
noncomputable def vectorToProjectiveSpace {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Spec ↧ℂ ⟶ ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
  Limits.pullback.lift (𝟙 _) (chartIntegralProj v hv) (Subsingleton.elim _ _)

/-- Rescaling homogeneous coordinates does not change the resulting projective-space
morphism. -/
lemma vectorToProjectiveSpace_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    vectorToProjectiveSpace (c • v) (smul_ne_zero hc hv) =
      vectorToProjectiveSpace v hv := by
  apply Limits.pullback.hom_ext
  · rw [vectorToProjectiveSpace, vectorToProjectiveSpace,
      Limits.pullback.lift_fst, Limits.pullback.lift_fst]
  · simp [vectorToProjectiveSpace, chartIntegralProj_smul v hv c hc]

@[simp]
lemma vectorToProjectiveSpace_toBase {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    vectorToProjectiveSpace v hv ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) = 𝟙 _ :=
  Limits.pullback.lift_fst _ _ _

/-- Nonzero homogeneous coordinates define a complex point of scheme-theoretic projective
space. -/
noncomputable def vectorToComplexPoint {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  Over.homMk (vectorToProjectiveSpace v hv) (vectorToProjectiveSpace_toBase v hv)

/-- Rescaling homogeneous coordinates does not change the resulting complex point. -/
lemma vectorToComplexPoint_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    vectorToComplexPoint (c • v) (smul_ne_zero hc hv) = vectorToComplexPoint v hv :=
  Over.OverMorphism.ext (vectorToProjectiveSpace_smul v hv c hc)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every complex point of scheme-theoretic projective space is represented by a nonzero
homogeneous coordinate vector. -/
lemma surjective_vectorToComplexPoint {n : ℕ} :
    Function.Surjective (fun v : {v : CoordinateSpace n // v ≠ 0} ↦
      vectorToComplexPoint v.1 v.2) := by
  intro z
  obtain ⟨v, hq⟩ := surjective_chartIntegralProj
    (z.left ≫ Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (UniversalGrading n))))
  change chartIntegralProj v.1 v.2 = _ at hq
  refine ⟨v, ?_⟩
  apply Over.OverMorphism.ext
  change vectorToProjectiveSpace v.1 v.2 = z.left
  apply Limits.pullback.hom_ext
  · change vectorToProjectiveSpace v.1 v.2 ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) =
        z.left ≫ ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)
    rw [vectorToProjectiveSpace_toBase]
    exact (Over.w z).symm
  · rw [vectorToProjectiveSpace, Limits.pullback.lift_snd]
    exact hq

/-- Homogeneous coordinates define an actual map from linear projectivization to the complex
points of scheme-theoretic projective space. -/
noncomputable def projectivizationToComplexPoint {n : ℕ} :
    Projectivization ℂ (CoordinateSpace n) →
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  Projectivization.lift
    (fun v ↦ vectorToComplexPoint v.1 v.2)
    (fun a b c h ↦ by
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [h, hc, zero_smul]
      simpa only [h] using vectorToComplexPoint_smul b.1 b.2 c hc)

@[simp]
lemma projectivizationToComplexPoint_mk {n : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0) :
    projectivizationToComplexPoint (Projectivization.mk ℂ v hv) =
      vectorToComplexPoint v hv :=
  rfl

/-- The coordinate map from linear projectivization onto the complex points of scheme-theoretic
projective space is surjective. -/
lemma surjective_projectivizationToComplexPoint {n : ℕ} :
    Function.Surjective (projectivizationToComplexPoint (n := n)) := by
  intro z
  obtain ⟨v, hz⟩ := surjective_vectorToComplexPoint z
  exact ⟨Projectivization.mk ℂ v.1 v.2, hz⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinate map from linear projectivization to scheme-theoretic projective-space complex
points is injective. -/
lemma injective_projectivizationToComplexPoint {n : ℕ} :
    Function.Injective (projectivizationToComplexPoint (n := n)) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | _ v hv =>
      induction q using Projectivization.ind with
      | _ w hw =>
          apply projectivization_mk_eq_of_chartIntegralProj_eq v w hv hw
          change vectorToComplexPoint v hv = vectorToComplexPoint w hw at hpq
          have hspace := congrArg Over.Hom.left hpq
          change vectorToProjectiveSpace v hv = vectorToProjectiveSpace w hw at hspace
          have hsnd := congrArg (fun f ↦ f ≫ Limits.pullback.snd
            (Limits.terminal.from (Spec ↧ℂ))
            (Limits.terminal.from (Proj (UniversalGrading n)))) hspace
          rw [vectorToProjectiveSpace, vectorToProjectiveSpace,
            Limits.pullback.lift_snd, Limits.pullback.lift_snd] at hsnd
          exact hsnd

noncomputable def chartPolynomialEvaluationHom {n : ℕ} (i : Fin (n + 1)) :
    UniversalRing n →+* MvPolynomial (Fin (n + 1)) ℂ :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ℂ →+* MvPolynomial (Fin (n + 1)) ℂ).comp
      ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom))
    (fun j ↦ if j = i then 1 else MvPolynomial.X j)

@[simp]
lemma chartPolynomialEvaluationHom_X_self {n : ℕ} (i : Fin (n + 1)) :
    chartPolynomialEvaluationHom i (MvPolynomial.X i) = 1 := by
  simp [chartPolynomialEvaluationHom]

noncomputable def chartAwayPolynomialHom {n : ℕ} (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+*
      MvPolynomial (Fin (n + 1)) ℂ :=
  (Localization.awayLift
    (chartPolynomialEvaluationHom i) (MvPolynomial.X i) (by
      rw [chartPolynomialEvaluationHom_X_self]
      exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma chartAwayPolynomialHom_chartCoordinate {n : ℕ} (i j : Fin (n + 1)) :
    chartAwayPolynomialHom i (chartCoordinate i j) =
      if j = i then 1 else MvPolynomial.X j := by
  unfold chartCoordinate
  simp only [chartAwayPolynomialHom, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift (chartPolynomialEvaluationHom i) (MvPolynomial.X i) _)
    (Localization.mk (MvPolynomial.X j) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (chartPolynomialEvaluationHom i) (MvPolynomial.X i)
    (MvPolynomial.X j) 1]
  simp [chartPolynomialEvaluationHom]
  rw [chartPolynomialEvaluationHom_X_self]
  simp

noncomputable def chartAffineToProj {n : ℕ} (i : Fin (n + 1)) :
    ComplexPoint.complexAffineSpace (Fin (n + 1)) ⟶ Proj (UniversalGrading n) :=
  (AffineSpace.SpecIso (Fin (n + 1)) ↧ℂ).hom ≫
    Spec.map (CommRingCat.ofHom (chartAwayPolynomialHom i)) ≫
    Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one

noncomputable def chartAffineToProjectiveSpace {n : ℕ} (i : Fin (n + 1)) :
    ComplexPoint.complexAffineSpace (Fin (n + 1)) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
  Limits.pullback.lift
    (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)
    (chartAffineToProj i) (Subsingleton.elim _ _)

@[reassoc]
lemma chartAffineToProjectiveSpace_over {n : ℕ} (i : Fin (n + 1)) :
    chartAffineToProjectiveSpace i ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) =
    ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma chartAffineToProjectiveSpace_toProj {n : ℕ} (i : Fin (n + 1)) :
    chartAffineToProjectiveSpace i ≫
      Limits.pullback.snd
        (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading n))) =
    chartAffineToProj i :=
  Limits.pullback.lift_snd _ _ _

noncomputable def chartAffineComplexPointMap {n : ℕ} (i : Fin (n + 1)) :
    ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) →
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  Point.map (Over.homMk (chartAffineToProjectiveSpace i)
    (chartAffineToProjectiveSpace_over i))

lemma continuous_chartAffineComplexPointMap {n : ℕ} (i : Fin (n + 1)) :
    @Continuous
      (ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)))
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
      Point.analyticTopology Point.analyticTopology
      (chartAffineComplexPointMap i) :=
  Point.continuous_map _

/-- Affine ratio coordinates associated to a vector in the `i`-th standard chart. -/
noncomputable def vectorChartRatios {n : ℕ} (i : Fin (n + 1))
    (v : {v : CoordinateSpace n // v i ≠ 0}) : CoordinateSpace n :=
  (v.1 i)⁻¹ • v.1

lemma continuous_vectorChartRatios {n : ℕ} (i : Fin (n + 1)) :
    Continuous (vectorChartRatios (n := n) i) := by
  unfold vectorChartRatios
  apply continuous_pi
  intro j
  have hci : Continuous (fun v : {v : CoordinateSpace n // v i ≠ 0} ↦ v.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hcj : Continuous (fun v : {v : CoordinateSpace n // v i ≠ 0} ↦ v.1 j) :=
    (continuous_apply j).comp continuous_subtype_val
  exact (hci.inv₀ (fun v ↦ v.property)).mul hcj

noncomputable def vectorChartToAffinePoint {n : ℕ} (i : Fin (n + 1)) :
    {v : CoordinateSpace n // v i ≠ 0} →
      ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) :=
  (ComplexPoint.affineSpaceEquiv (Fin (n + 1))).symm ∘ vectorChartRatios i

lemma continuous_vectorChartToAffinePoint {n : ℕ} (i : Fin (n + 1)) :
    @Continuous {v : CoordinateSpace n // v i ≠ 0}
      (ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)))
      inferInstance Point.analyticTopology
      (vectorChartToAffinePoint i) :=
  (ComplexPoint.affineSpaceHomeomorph (Fin (n + 1))).symm.continuous.comp
    (continuous_vectorChartRatios i)

lemma continuous_chartVectorToComplexPoint {n : ℕ} (i : Fin (n + 1)) :
    @Continuous {v : CoordinateSpace n // v i ≠ 0}
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
      inferInstance Point.analyticTopology
      (chartAffineComplexPointMap i ∘ vectorChartToAffinePoint i) := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))) :=
    Point.analyticTopology
  let : TopologicalSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
    Point.analyticTopology
  exact (continuous_chartAffineComplexPointMap i).comp
    (continuous_vectorChartToAffinePoint i)

lemma specPreimage_apply {R : CommRingCat} (f : Spec ↧ℂ ⟶ Spec R) (r : R) :
    (Spec.preimage f).hom r =
      (Scheme.ΓSpecIso ↧ℂ).hom
        (f.appTop ((Scheme.ΓSpecIso R).inv r)) := by
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage f)
  rw [Spec.map_preimage] at h
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso R).inv r)
  simpa using h'.symm

set_option backward.isDefEq.respectTransparency.types false in
lemma vectorChartToAffinePoint_comp_SpecIso {n : ℕ} (i : Fin (n + 1))
    (v : {v : CoordinateSpace n // v i ≠ 0}) :
    (vectorChartToAffinePoint i v).left ≫
        (AffineSpace.SpecIso (Fin (n + 1)) ↧ℂ).hom =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (vectorChartRatios i v))) := by
  rw [← Spec.map_preimage ((vectorChartToAffinePoint i v).left ≫
    (AffineSpace.SpecIso (Fin (n + 1)) ↧ℂ).hom)]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [specPreimage_apply]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [ComplexPoint.SpecIso_hom_appTop_C]
    change (Scheme.ΓSpecIso ↧ℂ).hom
      ((((ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ).appTop ≫
        (vectorChartToAffinePoint i v).left.appTop))
          ((Scheme.ΓSpecIso ↧ℂ).inv c)) = _
    rw [← Scheme.Hom.comp_appTop, show (vectorChartToAffinePoint i v).left ≫
      (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ) = 𝟙 _ from
        Over.w (vectorChartToAffinePoint i v)]
    simp
  · intro j
    rw [specPreimage_apply]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [ComplexPoint.SpecIso_hom_appTop_X]
    change (Scheme.ΓSpecIso ↧ℂ).hom
      ((vectorChartToAffinePoint i v).left.appTop
        (AffineSpace.coord (Spec ↧ℂ) j)) = _
    simp [vectorChartToAffinePoint, ComplexPoint.affineSpaceEquiv]

set_option backward.isDefEq.respectTransparency.types false in
lemma chartAwayPolynomialHom_evaluate_ratios {n : ℕ} (i : Fin (n + 1))
    (v : {v : CoordinateSpace n // v i ≠ 0}) :
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) (vectorChartRatios i v)).comp
        (chartAwayPolynomialHom i) =
      awayCoordinateEvaluation v.1 i v.2 := by
  apply awayRingHom_ext i
  · intro a
    exact DFunLike.congr_fun (degreeZero_ringHom_unique
      (((MvPolynomial.eval₂Hom (RingHom.id ℂ) (vectorChartRatios i v)).comp
        (chartAwayPolynomialHom i)).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
            (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))
      ((awayCoordinateEvaluation v.1 i v.2).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i : UniversalRing n))))) a
  · intro j
    rw [RingHom.comp_apply, chartAwayPolynomialHom_chartCoordinate]
    change _ = awayCoordinateEvaluation v.1 i v.2
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _)
    rw [awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j)]
    simp only [coordinateEvaluationHom_X]
    by_cases hji : j = i
    · subst j
      simp [vectorChartRatios, v.2]
    · simp [hji, vectorChartRatios]
      ring

set_option backward.isDefEq.respectTransparency.types false in
lemma vectorChartToAffinePoint_comp_chartAffineToProj {n : ℕ} (i : Fin (n + 1))
    (v : {v : CoordinateSpace n // v i ≠ 0}) :
    (vectorChartToAffinePoint i v).left ≫ chartAffineToProj i =
      chartIntegralProjAt v.1 i v.2 := by
  unfold chartAffineToProj chartIntegralProjAt
  rw [← Category.assoc, vectorChartToAffinePoint_comp_SpecIso, ← Category.assoc,
    ← Spec.map_comp, show CommRingCat.ofHom (chartAwayPolynomialHom i) ≫
      CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (vectorChartRatios i v)) =
      CommRingCat.ofHom (awayCoordinateEvaluation v.1 i v.2) from
    CommRingCat.hom_ext (chartAwayPolynomialHom_evaluate_ratios i v)]

lemma vector_ne_zero_of_coordinate {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) : v ≠ 0 :=
  fun h ↦ hi (congrFun h i)

@[reassoc]
lemma vectorToProjectiveSpace_toProj {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    vectorToProjectiveSpace v hv ≫
      Limits.pullback.snd
        (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading n))) =
    chartIntegralProj v hv :=
  Limits.pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma chartVectorToComplexPoint_eq {n : ℕ} (i : Fin (n + 1))
    (v : {v : CoordinateSpace n // v i ≠ 0}) :
    chartAffineComplexPointMap i (vectorChartToAffinePoint i v) =
      vectorToComplexPoint v.1 (vector_ne_zero_of_coordinate v.1 i v.2) := by
  apply Over.OverMorphism.ext
  change (vectorChartToAffinePoint i v).left ≫ chartAffineToProjectiveSpace i =
    vectorToProjectiveSpace v.1 (vector_ne_zero_of_coordinate v.1 i v.2)
  apply Limits.pullback.hom_ext
  · change ((vectorChartToAffinePoint i v).left ≫ chartAffineToProjectiveSpace i) ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) =
      vectorToProjectiveSpace v.1 (vector_ne_zero_of_coordinate v.1 i v.2) ≫
        ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)
    calc
      _ = (vectorChartToAffinePoint i v).left ≫
          (chartAffineToProjectiveSpace i ≫
            ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) :=
        Category.assoc _ _ _
      _ = (vectorChartToAffinePoint i v).left ≫
          (ComplexPoint.complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ) := by
        rw [chartAffineToProjectiveSpace_over]
      _ = 𝟙 _ := Over.w (vectorChartToAffinePoint i v)
      _ = _ := (vectorToProjectiveSpace_toBase _ _).symm
  · calc
      _ = (vectorChartToAffinePoint i v).left ≫
          (chartAffineToProjectiveSpace i ≫ Limits.pullback.snd
            (Limits.terminal.from (Spec ↧ℂ))
            (Limits.terminal.from (Proj (UniversalGrading n)))) :=
        Category.assoc _ _ _
      _ = (vectorChartToAffinePoint i v).left ≫ chartAffineToProj i := by
        rw [chartAffineToProjectiveSpace_toProj]
      _ = chartIntegralProjAt v.1 i v.2 :=
        vectorChartToAffinePoint_comp_chartAffineToProj i v
      _ = chartIntegralProj v.1 (vector_ne_zero_of_coordinate v.1 i v.2) :=
        (chartIntegralProj_eq_chartIntegralProjAt v.1
          (vector_ne_zero_of_coordinate v.1 i v.2) i v.2).symm
      _ = _ := (vectorToProjectiveSpace_toProj _ _).symm

/-- Nonzero vectors whose `i`-th coordinate is nonzero. -/
def nonzeroVectorChart {n : ℕ} (i : Fin (n + 1)) :
    Set {v : CoordinateSpace n // v ≠ 0} :=
  {v | v.1 i ≠ 0}

/-- Forget the redundant global nonvanishing proof on a standard coordinate chart. -/
def toVectorChart {n : ℕ} (i : Fin (n + 1))
    (v : nonzeroVectorChart i) : {v : CoordinateSpace n // v i ≠ 0} :=
  ⟨v.1.1, v.2⟩

lemma continuous_toVectorChart {n : ℕ} (i : Fin (n + 1)) :
    Continuous (toVectorChart i) :=
  continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

lemma isOpen_nonzeroVectorChart {n : ℕ} (i : Fin (n + 1)) :
    IsOpen (nonzeroVectorChart i) :=
  isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)

lemma iUnion_nonzeroVectorChart {n : ℕ} :
    ⋃ i : Fin (n + 1), nonzeroVectorChart i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  rw [Set.mem_iUnion]
  by_contra h
  apply v.2
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

lemma continuousOn_vectorToComplexPoint_chart {n : ℕ} (i : Fin (n + 1)) :
    @ContinuousOn {v : CoordinateSpace n // v ≠ 0}
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
      inferInstance Point.analyticTopology
      (fun v ↦ vectorToComplexPoint v.1 v.2) (nonzeroVectorChart i) := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
    Point.analyticTopology
  rw [continuousOn_iff_continuous_domRestrict]
  have h := (continuous_chartVectorToComplexPoint i).comp
    (continuous_toVectorChart i)
  exact h.congr fun v ↦ chartVectorToComplexPoint_eq i (toVectorChart i v)

lemma continuous_vectorToComplexPoint {n : ℕ} :
    @Continuous {v : CoordinateSpace n // v ≠ 0}
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
      inferInstance Point.analyticTopology
      (fun v ↦ vectorToComplexPoint v.1 v.2) := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
    Point.analyticTopology
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (continuousOn_vectorToComplexPoint_chart (n := n))
    (isOpen_nonzeroVectorChart (n := n))
    iUnion_nonzeroVectorChart

lemma continuous_projectivizationToComplexPoint {n : ℕ} :
    @Continuous (Projectivization ℂ (CoordinateSpace n))
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
      (instTopologicalSpace n) Point.analyticTopology
      projectivizationToComplexPoint := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
    Point.analyticTopology
  apply Continuous.quotient_lift
  exact continuous_vectorToComplexPoint

/-- The analytic topology on the complex points of finite-dimensional scheme-theoretic
projective space. -/
noncomputable instance instTopologicalSpaceProjectiveSpaceComplexPoint (n : ℕ) :
    TopologicalSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  Point.analyticTopology

/-- Finite-dimensional scheme-theoretic complex projective space is analytically compact. -/
noncomputable instance instCompactSpaceProjectiveSpaceComplexPoint (n : ℕ) :
    CompactSpace
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) := by
  constructor
  rw [← (surjective_projectivizationToComplexPoint (n := n)).range_eq]
  exact isCompact_range continuous_projectivizationToComplexPoint

end ComplexProjectiveSpace

end AlgebraicGeometry
