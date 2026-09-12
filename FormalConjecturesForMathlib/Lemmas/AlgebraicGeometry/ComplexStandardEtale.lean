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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexAffineScheme
public import Mathlib.RingTheory.Etale.StandardEtale

import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Complex points of standard étale algebras

A complex point of a standard étale algebra over a polynomial ring is a base point together with
a root of the defining polynomial at which the localization polynomial does not vanish. This file
constructs that correspondence as a homeomorphism. The inverse continuity proof evaluates an
arbitrary representative in the explicit bivariate-polynomial quotient presentation.

Like `ComplexLocalization`, this works throughout with `ℂ`-algebra homomorphisms rather than with
complex points of schemes, so it lives in namespace `AlgebraicGeometry.ComplexAlgHom`.
-/

@[expose] public section

open scoped Polynomial

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexAlgHom

open ComplexPoint Point

noncomputable section

/-- The polynomial coordinate ring of complex affine `n`-space. -/
abbrev complexPolynomialRing (n : ℕ) := MvPolynomial (Fin n) ℂ

/-- A complex algebra homomorphism out of a polynomial ring is determined by the images of its
variables. -/
def mvPolynomialAlgHomEquiv (n : ℕ) :
    (complexPolynomialRing n →ₐ[ℂ] ℂ) ≃ (Fin n → ℂ) where
  toFun φ i := φ (MvPolynomial.X i)
  invFun v := MvPolynomial.aeval v
  left_inv φ := MvPolynomial.algHom_ext fun i ↦ by simp
  right_inv v := funext fun i ↦ by simp

lemma continuous_mvPolynomialAlgHomEquiv (n : ℕ) :
    Continuous (mvPolynomialAlgHomEquiv n) :=
  continuous_pi fun i ↦
    continuous_affineAlgebraHom_apply (complexPolynomialRing n) (MvPolynomial.X i)

lemma continuous_mvPolynomialAlgHomEquiv_symm (n : ℕ) :
    Continuous (mvPolynomialAlgHomEquiv n).symm := by
  rw [continuous_induced_rng]
  refine continuous_pi fun p ↦ ?_
  simpa [mvPolynomialAlgHomEquiv] using p.continuous_eval

/-- Pointwise convergence on complex algebra homomorphisms out of a polynomial ring is the usual
Euclidean topology on the tuple of variable values. -/
def mvPolynomialAlgHomHomeomorph (n : ℕ) :
    (complexPolynomialRing n →ₐ[ℂ] ℂ) ≃ₜ (Fin n → ℂ) where
  toEquiv := mvPolynomialAlgHomEquiv n
  continuous_toFun := continuous_mvPolynomialAlgHomEquiv n
  continuous_invFun := continuous_mvPolynomialAlgHomEquiv_symm n

variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- The complex algebra structure on a standard étale algebra over a complex polynomial ring. -/
noncomputable instance standardEtaleRingAlgebra : Algebra ℂ P.Ring :=
  ((algebraMap (complexPolynomialRing n) P.Ring).comp
    (algebraMap ℂ (complexPolynomialRing n))).toAlgebra

noncomputable instance standardEtaleRingIsScalarTower :
    IsScalarTower ℂ (complexPolynomialRing n) P.Ring :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- A base point and a root satisfying the equations represented by a standard étale pair. -/
abbrev standardEtalePointSpace :=
  { vx : ((complexPolynomialRing n →ₐ[ℂ] ℂ) × ℂ) //
    Polynomial.eval₂ vx.1 vx.2 P.f = 0 ∧ Polynomial.eval₂ vx.1 vx.2 P.g ≠ 0 }

/-- Construct a complex algebra homomorphism from the root data of a standard étale point. -/
def standardEtalePointToAlgHom (z : standardEtalePointSpace P) : P.Ring →ₐ[ℂ] ℂ := by
  letI : Algebra (complexPolynomialRing n) ℂ := z.1.1.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (complexPolynomialRing n) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (z.1.1.commutes c).symm
  have hz : P.HasMap z.1.2 := by
    rw [StandardEtalePair.HasMap]
    constructor
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using z.2.1
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, isUnit_iff_ne_zero] using z.2.2
  exact (P.lift z.1.2 hz).restrictScalars ℂ

/-- Read the base point and distinguished root from a complex point of a standard étale algebra. -/
def algHomToStandardEtalePoint (φ : P.Ring →ₐ[ℂ] ℂ) : standardEtalePointSpace P := by
  let v : complexPolynomialRing n →ₐ[ℂ] ℂ :=
    φ.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) P.Ring)
  let x := φ P.X
  refine ⟨(v, x), ?_⟩
  let : Algebra (complexPolynomialRing n) ℂ := v.toRingHom.toAlgebra
  let φB : P.Ring →ₐ[complexPolynomialRing n] ℂ :=
    { toRingHom := φ.toRingHom
      commutes' b := rfl }
  have h := P.hasMap_X.map φB
  constructor
  · simpa [v, x, φB, StandardEtalePair.HasMap, Polynomial.aeval_def,
      RingHom.algebraMap_toAlgebra] using h.1
  · simpa [v, x, φB, StandardEtalePair.HasMap, Polynomial.aeval_def,
      RingHom.algebraMap_toAlgebra, isUnit_iff_ne_zero] using h.2

/-- Complex algebra homomorphisms out of a standard étale algebra are equivalent to its root
data. -/
def standardEtalePointEquiv :
    (P.Ring →ₐ[ℂ] ℂ) ≃ standardEtalePointSpace P where
  toFun := algHomToStandardEtalePoint P
  invFun := standardEtalePointToAlgHom P
  left_inv φ := by
    let v : complexPolynomialRing n →ₐ[ℂ] ℂ :=
      φ.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) P.Ring)
    let : Algebra (complexPolynomialRing n) ℂ := v.toRingHom.toAlgebra
    let hscalar : IsScalarTower ℂ (complexPolynomialRing n) ℂ :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (v.commutes c).symm
    let := hscalar
    let φB : P.Ring →ₐ[complexPolynomialRing n] ℂ :=
      { toRingHom := φ.toRingHom
        commutes' b := rfl }
    have heq : P.lift (φ P.X) (P.hasMap_X.map φB) = φB :=
      P.hom_ext (by simp [φB])
    have hres := congrArg
      (fun q : P.Ring →ₐ[complexPolynomialRing n] ℂ ↦ q.restrictScalars ℂ) heq
    have hφ : φB.restrictScalars ℂ = φ := AlgHom.ext fun _ ↦ rfl
    change (P.lift (φ P.X) (P.hasMap_X.map φB)).restrictScalars ℂ = φ
    exact hres.trans hφ
  right_inv z := by
    let : Algebra (complexPolynomialRing n) ℂ := z.1.1.toRingHom.toAlgebra
    let hscalar : IsScalarTower ℂ (complexPolynomialRing n) ℂ :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (z.1.1.commutes c).symm
    let := hscalar
    have hz : P.HasMap z.1.2 := by
      rw [StandardEtalePair.HasMap]
      constructor
      · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using z.2.1
      · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, isUnit_iff_ne_zero] using z.2.2
    apply Subtype.ext
    apply Prod.ext
    · refine AlgHom.ext fun b ↦ ?_
      change P.lift z.1.2 hz (algebraMap (complexPolynomialRing n) P.Ring b) = z.1.1 b
      exact (P.lift z.1.2 hz).commutes b
    · change P.lift z.1.2 hz P.X = z.1.2
      exact P.lift_X _ _

lemma continuous_algHomToStandardEtalePoint :
    Continuous (algHomToStandardEtalePoint P) := by
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · rw [continuous_induced_rng]
    refine continuous_pi fun b ↦ ?_
    simpa [algHomToStandardEtalePoint] using
      continuous_affineAlgebraHom_apply P.Ring
        (algebraMap (complexPolynomialRing n) P.Ring b)
  · simpa [algHomToStandardEtalePoint] using
      continuous_affineAlgebraHom_apply P.Ring P.X

/-- Polynomial evaluation is continuous when both the coefficient homomorphism and the argument
vary. -/
lemma continuous_eval₂_varying (p : (complexPolynomialRing n)[X]) :
    Continuous (fun vx : (complexPolynomialRing n →ₐ[ℂ] ℂ) × ℂ ↦
      Polynomial.eval₂ vx.1 vx.2 p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun vx : (complexPolynomialRing n →ₐ[ℂ] ℂ) × ℂ ↦
          Polynomial.eval₂ vx.1 vx.2 (p + q)) =
          (fun vx ↦ Polynomial.eval₂ vx.1 vx.2 p +
            Polynomial.eval₂ vx.1 vx.2 q) by
        funext vx
        simp]
      exact hp.add hq
  | monomial k a =>
      rw [show (fun vx : (complexPolynomialRing n →ₐ[ℂ] ℂ) × ℂ ↦
          Polynomial.eval₂ vx.1 vx.2 (Polynomial.monomial k a)) =
          (fun vx ↦ vx.1 a * vx.2 ^ k) by
        funext vx
        simp]
      exact
        ((continuous_affineAlgebraHom_apply (complexPolynomialRing n) a).comp continuous_fst).mul
          (continuous_snd.pow k)

/-- Evaluation of a quotient representative under the standard étale point map. -/
lemma standardEtalePointToAlgHom_mk (z : standardEtalePointSpace P)
    (q : (complexPolynomialRing n)[X][X]) :
    standardEtalePointToAlgHom P z (Ideal.Quotient.mk _ q) =
      Polynomial.eval₂
        (Polynomial.eval₂RingHom z.1.1 z.1.2)
        (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ q := by
  let : Algebra (complexPolynomialRing n) ℂ := z.1.1.toRingHom.toAlgebra
  let hscalar : IsScalarTower ℂ (complexPolynomialRing n) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (z.1.1.commutes c).symm
  let := hscalar
  have hz : P.HasMap z.1.2 := by
    rw [StandardEtalePair.HasMap]
    constructor
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using z.2.1
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, isUnit_iff_ne_zero] using z.2.2
  change P.lift z.1.2 hz (Ideal.Quotient.mk _ q) = _
  unfold StandardEtalePair.lift
  change Polynomial.aevalAeval z.1.2 (↑hz.2.unit⁻¹ : ℂ) q = _
  have hinv : (↑hz.2.unit⁻¹ : ℂ) =
      (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ := by
    calc
      (↑hz.2.unit⁻¹ : ℂ) = (↑hz.2.unit : ℂ)⁻¹ := by simp
      _ = (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ := by
        congr 1
  rw [hinv]
  have heq :
      (Polynomial.aevalAeval z.1.2
        (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹).toRingHom =
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom z.1.1.toRingHom z.1.2)
        (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ := by
    ext b <;> simp [Polynomial.aevalAeval, Polynomial.aevalAevalEquiv,
      Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
  exact DFunLike.congr_fun heq q

lemma continuous_standardEtale_bivariate_evaluation
    (q : (complexPolynomialRing n)[X][X]) :
    Continuous (fun z : standardEtalePointSpace P ↦
      Polynomial.eval₂
        (Polynomial.eval₂RingHom z.1.1 z.1.2)
        (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ q) := by
  have hg : Continuous (fun z : standardEtalePointSpace P ↦
      Polynomial.eval₂ z.1.1 z.1.2 P.g) :=
    (continuous_eval₂_varying P.g).comp continuous_subtype_val
  have hginv : Continuous (fun z : standardEtalePointSpace P ↦
      (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹) :=
    hg.inv₀ fun z ↦ z.2.2
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [show (fun z : standardEtalePointSpace P ↦
          Polynomial.eval₂ (Polynomial.eval₂RingHom z.1.1 z.1.2)
            (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ (q + r)) =
          (fun z ↦
            Polynomial.eval₂ (Polynomial.eval₂RingHom z.1.1 z.1.2)
              (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ q +
            Polynomial.eval₂ (Polynomial.eval₂RingHom z.1.1 z.1.2)
              (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ r) by
        funext z
        simp]
      exact hq.add hr
  | monomial k a =>
      rw [show (fun z : standardEtalePointSpace P ↦
          Polynomial.eval₂ (Polynomial.eval₂RingHom z.1.1 z.1.2)
            (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ (Polynomial.monomial k a)) =
          (fun z ↦ Polynomial.eval₂ z.1.1 z.1.2 a *
            (Polynomial.eval₂ z.1.1 z.1.2 P.g)⁻¹ ^ k) by
        funext z
        simp]
      exact ((continuous_eval₂_varying a).comp continuous_subtype_val).mul (hginv.pow k)

lemma continuous_standardEtalePointToAlgHom :
    Continuous (standardEtalePointToAlgHom P) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun r ↦ ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
  simpa only [Function.comp_apply, standardEtalePointToAlgHom_mk] using
    continuous_standardEtale_bivariate_evaluation P q

/-- The pointwise topology on homomorphisms out of a standard étale algebra is the topology on
its explicit root data. -/
def standardEtalePointHomeomorph :
    (P.Ring →ₐ[ℂ] ℂ) ≃ₜ standardEtalePointSpace P where
  toEquiv := standardEtalePointEquiv P
  continuous_toFun := continuous_algHomToStandardEtalePoint P
  continuous_invFun := continuous_standardEtalePointToAlgHom P

/-- The standard étale equations written in ordinary complex coordinates. -/
abbrev standardEtaleCoordinateSpace :=
  { vx : ((Fin n → ℂ) × ℂ) //
    Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 P.f = 0 ∧
      Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 P.g ≠ 0 }

/-- Replace the polynomial-ring homomorphism in standard étale root data by its tuple of variable
values. -/
def standardEtalePointCoordinateHomeomorph :
    standardEtalePointSpace P ≃ₜ standardEtaleCoordinateSpace P :=
  ((mvPolynomialAlgHomHomeomorph n).prodCongr (Homeomorph.refl ℂ)).subtype fun z ↦ by
    have h := (mvPolynomialAlgHomEquiv n).left_inv z.1
    simpa [mvPolynomialAlgHomHomeomorph, mvPolynomialAlgHomEquiv] using
      congrArg (fun φ : complexPolynomialRing n →ₐ[ℂ] ℂ ↦
        (Polynomial.eval₂ φ z.2 P.f = 0 ∧ Polynomial.eval₂ φ z.2 P.g ≠ 0)) h.symm

/-- Complex points of a standard étale algebra as the corresponding equation locus in ordinary
complex coordinates. -/
def standardEtaleCoordinateHomeomorph :
    (P.Ring →ₐ[ℂ] ℂ) ≃ₜ standardEtaleCoordinateSpace P :=
  (standardEtalePointHomeomorph P).trans (standardEtalePointCoordinateHomeomorph P)

end

end AlgebraicGeometry.ComplexAlgHom
