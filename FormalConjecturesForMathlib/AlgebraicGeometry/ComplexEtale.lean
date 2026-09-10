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
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexLocalization
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexStandardEtale
public import Mathlib.Analysis.Calculus.ContDiff.RCLike -- shake: keep
public import Mathlib.Analysis.Calculus.Deriv.Polynomial -- shake: keep
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Complex points of étale morphisms

The complex points of a standard étale algebra over a polynomial ring form the zero locus of
one polynomial with nonzero derivative in its distinguished variable. The complex implicit
function theorem gives explicit local charts in which projection to the polynomial coordinates
is a homeomorphism. This file constructs those charts and transports the result to the associated
affine schemes.

The charts themselves are statements about `ℂ`-algebra homomorphisms and live in namespace
`AlgebraicGeometry.ComplexAlgHom`; only the last section, which transports them to schemes, is in
`AlgebraicGeometry.ComplexPoint`.
-/

@[expose] public section

open scoped Polynomial Topology ContDiff

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexAlgHom

open ComplexPoint Point

noncomputable section

variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- The equation defining a standard étale algebra, evaluated in ordinary complex
coordinates. -/
def standardEtaleEquation (vx : (Fin n → ℂ) × ℂ) : ℂ :=
  Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 P.f

/-- Evaluating a polynomial whose coefficients are multivariate complex polynomials is analytic in
both the coefficient variables and the distinguished polynomial variable. -/
lemma analyticAt_polynomialEvaluation
    (p : (complexPolynomialRing n)[X]) (u : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ
      (fun vx ↦ Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 p) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun vx : (Fin n → ℂ) × ℂ ↦
          Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 (p + q)) =
          (fun vx ↦
            Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 p +
            Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2 q) by
        funext vx
        simp]
      exact hp.add hq
  | monomial k a =>
      rw [show (fun vx : (Fin n → ℂ) × ℂ ↦
          Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) vx.1).toRingHom vx.2
            (Polynomial.monomial k a)) =
          (fun vx ↦ MvPolynomial.eval vx.1 a * vx.2 ^ k) by
        funext vx
        simp]
      have ha : AnalyticAt ℂ (fun z : Fin n → ℂ ↦ MvPolynomial.eval z a) u.1 :=
        AnalyticOnNhd.eval_mvPolynomial a u.1 (Set.mem_univ _)
      exact (ha.comp (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ) u)).mul
        ((ContinuousLinearMap.analyticAt
          (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) u).pow k)

lemma analyticAt_standardEtaleEquation (u : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (standardEtaleEquation P) u :=
  analyticAt_polynomialEvaluation P.f u

lemma contDiffAt_standardEtaleEquation (u : (Fin n → ℂ) × ℂ) :
    ContDiffAt ℂ ∞ (standardEtaleEquation P) u :=
  (analyticAt_standardEtaleEquation P u).contDiffAt

/-- The defining polynomial after specializing the polynomial-ring coordinates. -/
def standardEtaleFiberPolynomial (z : Fin n → ℂ) : ℂ[X] :=
  P.f.map (MvPolynomial.eval z)

lemma standardEtaleEquation_eq_eval (u : (Fin n → ℂ) × ℂ) :
    standardEtaleEquation P u = (standardEtaleFiberPolynomial P u.1).eval u.2 := by
  simp [standardEtaleEquation, standardEtaleFiberPolynomial, Polynomial.eval_map]

/-- The distinguished derivative is nonzero at every complex point of a standard étale
algebra. -/
lemma standardEtale_fiberDerivative_ne_zero (z : standardEtaleCoordinateSpace P) :
    Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) z.1.1).toRingHom z.1.2
      P.f.derivative ≠ 0 := by
  let : Algebra (complexPolynomialRing n) ℂ :=
    (MvPolynomial.aeval (R := ℂ) z.1.1).toRingHom.toAlgebra
  have hz : P.HasMap z.1.2 := by
    rw [StandardEtalePair.HasMap]
    constructor
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using z.2.1
    · simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra,
        isUnit_iff_ne_zero] using z.2.2
  have hunit := hz.isUnit_derivative_f
  simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hunit.ne_zero

lemma fderiv_standardEtaleEquation_comp_inr (u : (Fin n → ℂ) × ℂ) :
    fderiv ℂ (standardEtaleEquation P) u ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) u.1).toRingHom u.2
          P.f.derivative) := by
  have hins : HasFDerivAt (fun t : ℂ ↦ (u.1, t))
      (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) u.2 :=
    (hasFDerivAt_const u.1 u.2).prodMk (hasFDerivAt_id u.2)
  have hchain :=
    (((contDiffAt_standardEtaleEquation P u).differentiableAt (by simp)).hasFDerivAt).comp u.2 hins
  have hchain' : HasFDerivAt (fun t : ℂ ↦ (standardEtaleFiberPolynomial P u.1).eval t)
      (fderiv ℂ (standardEtaleEquation P) u ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) u.2 := by
    simpa [Function.comp_def, standardEtaleEquation_eq_eval] using hchain
  have hpoly := (standardEtaleFiberPolynomial P u.1).hasFDerivAt u.2
  simpa [standardEtaleFiberPolynomial, Polynomial.derivative_map, Polynomial.eval_map] using
    hchain'.unique hpoly

lemma standardEtale_partial_isInvertible (z : standardEtaleCoordinateSpace P) :
    (fderiv ℂ (standardEtaleEquation P) z.1 ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  rw [fderiv_standardEtaleEquation_comp_inr]
  let d := Polynomial.eval₂
    (MvPolynomial.eval z.1.1) z.1.2 P.f.derivative
  have hd : d ≠ 0 := by
    simpa [d] using standardEtale_fiberDerivative_ne_zero P z
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

/-- The ambient implicit-function chart sending `(z, t)` to `(f(z, t), z)`. -/
def standardEtaleImplicitOpenPartialHomeomorph (z : standardEtaleCoordinateSpace P) :
    OpenPartialHomeomorph ((Fin n → ℂ) × ℂ) (ℂ × (Fin n → ℂ)) :=
  let cdf := contDiffAt_standardEtaleEquation P z.1
  let hs := cdf.hasStrictFDerivAt (by simp)
  (hs.implicitFunctionDataOfProdDomain
    (standardEtale_partial_isInvertible P z)).toOpenPartialHomeomorph

@[simp]
lemma standardEtaleImplicitOpenPartialHomeomorph_apply
    (z : standardEtaleCoordinateSpace P) (u : (Fin n → ℂ) × ℂ) :
    standardEtaleImplicitOpenPartialHomeomorph P z u =
      (standardEtaleEquation P u, u.1) := by
  let cdf := contDiffAt_standardEtaleEquation P z.1
  let hs := cdf.hasStrictFDerivAt (by simp)
  let φ : ImplicitFunctionData ℂ ((Fin n → ℂ) × ℂ) ℂ (Fin n → ℂ) :=
    hs.implicitFunctionDataOfProdDomain (standardEtale_partial_isInvertible P z)
  change φ.toOpenPartialHomeomorph u = _
  rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
  simp [φ]

lemma standardEtale_mem_implicit_source (z : standardEtaleCoordinateSpace P) :
    z.1 ∈ (standardEtaleImplicitOpenPartialHomeomorph P z).source := by
  let cdf := contDiffAt_standardEtaleEquation P z.1
  let hs := cdf.hasStrictFDerivAt (by simp)
  let φ : ImplicitFunctionData ℂ ((Fin n → ℂ) × ℂ) ℂ (Fin n → ℂ) :=
    hs.implicitFunctionDataOfProdDomain (standardEtale_partial_isInvertible P z)
  simpa [standardEtaleImplicitOpenPartialHomeomorph, φ] using
    φ.pt_mem_toOpenPartialHomeomorph_source

lemma standardEtale_zero_base_mem_implicit_target (z : standardEtaleCoordinateSpace P) :
    (0, z.1.1) ∈ (standardEtaleImplicitOpenPartialHomeomorph P z).target := by
  have hzmap := (standardEtaleImplicitOpenPartialHomeomorph P z).map_source
    (standardEtale_mem_implicit_source P z)
  have heq : standardEtaleEquation P z.1 = 0 := by
    simpa [standardEtaleEquation] using z.2.1
  rw [standardEtaleImplicitOpenPartialHomeomorph_apply, heq] at hzmap
  exact hzmap

/-- The localization polynomial evaluated in ordinary complex coordinates. -/
def standardEtaleLocalizationEquation (u : (Fin n → ℂ) × ℂ) : ℂ :=
  Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) u.1).toRingHom u.2 P.g

lemma analyticAt_standardEtaleLocalizationEquation (u : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (standardEtaleLocalizationEquation P) u :=
  analyticAt_polynomialEvaluation P.g u

/-- Evaluate a representative of the double-polynomial presentation of a standard étale
algebra in ordinary complex coordinates. The outer variable is sent to the inverse of the
localization polynomial. -/
def standardEtaleBivariateEvaluation
    (q : (complexPolynomialRing n)[X][X]) (u : (Fin n → ℂ) × ℂ) : ℂ :=
  Polynomial.eval₂
    (Polynomial.eval₂RingHom (MvPolynomial.aeval (R := ℂ) u.1).toRingHom u.2)
    (standardEtaleLocalizationEquation P u)⁻¹ q

/-- Evaluation of every representative of the standard étale presentation is analytic wherever
the localization polynomial is nonzero. -/
lemma analyticAt_standardEtaleBivariateEvaluation
    (q : (complexPolynomialRing n)[X][X]) (u : (Fin n → ℂ) × ℂ)
    (hu : standardEtaleLocalizationEquation P u ≠ 0) :
    AnalyticAt ℂ (standardEtaleBivariateEvaluation P q) u := by
  have hginv : AnalyticAt ℂ (fun v ↦ (standardEtaleLocalizationEquation P v)⁻¹) u :=
    (analyticAt_standardEtaleLocalizationEquation P u).inv hu
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [show standardEtaleBivariateEvaluation P (q + r) =
          fun v ↦ standardEtaleBivariateEvaluation P q v +
            standardEtaleBivariateEvaluation P r v by
        funext v
        simp [standardEtaleBivariateEvaluation]]
      exact hq.add hr
  | monomial k a =>
      rw [show standardEtaleBivariateEvaluation P (Polynomial.monomial k a) =
          fun v ↦
            Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) v.1).toRingHom v.2 a *
              (standardEtaleLocalizationEquation P v)⁻¹ ^ k by
        funext v
        simp [standardEtaleBivariateEvaluation]]
      exact (analyticAt_polynomialEvaluation a u).mul (hginv.pow k)

lemma continuous_standardEtaleLocalizationEquation :
    Continuous (standardEtaleLocalizationEquation P) := by
  have hcoord : Continuous (fun u : (Fin n → ℂ) × ℂ ↦
      ((mvPolynomialAlgHomHomeomorph n).symm u.1, u.2)) :=
    ((mvPolynomialAlgHomHomeomorph n).symm.continuous.comp continuous_fst).prodMk continuous_snd
  exact (continuous_eval₂_varying P.g).comp hcoord

/-- The source of the standard étale chart centered at `z`. -/
def standardEtaleChartSource (z : standardEtaleCoordinateSpace P) :
    Set (standardEtaleCoordinateSpace P) :=
  Subtype.val ⁻¹' (standardEtaleImplicitOpenPartialHomeomorph P z).source

/-- The target of the standard étale chart centered at `z`. The second condition retains the
localization defining the standard étale algebra. -/
def standardEtaleChartTarget (z : standardEtaleCoordinateSpace P) : Set (Fin n → ℂ) :=
  {w | (0, w) ∈ (standardEtaleImplicitOpenPartialHomeomorph P z).target ∧
    standardEtaleLocalizationEquation P
      ((standardEtaleImplicitOpenPartialHomeomorph P z).symm (0, w)) ≠ 0}

lemma isOpen_standardEtaleChartSource (z : standardEtaleCoordinateSpace P) :
    IsOpen (standardEtaleChartSource P z) :=
  (standardEtaleImplicitOpenPartialHomeomorph P z).open_source.preimage continuous_subtype_val

lemma isOpen_standardEtaleChartTarget (z : standardEtaleCoordinateSpace P) :
    IsOpen (standardEtaleChartTarget P z) := by
  let T := standardEtaleImplicitOpenPartialHomeomorph P z
  let zeroSection : (Fin n → ℂ) → ℂ × (Fin n → ℂ) := fun w ↦ (0, w)
  let targetZero : Set (Fin n → ℂ) := zeroSection ⁻¹' T.target
  have hzero : Continuous zeroSection := continuous_const.prodMk continuous_id
  have htargetZero : IsOpen targetZero := T.open_target.preimage hzero
  have hinv : ContinuousOn (fun w : Fin n → ℂ ↦ T.symm (zeroSection w)) targetZero :=
    T.continuousOn_invFun.comp hzero.continuousOn fun _ hw ↦ hw
  have hloc : ContinuousOn
      (fun w : Fin n → ℂ ↦ standardEtaleLocalizationEquation P (T.symm (zeroSection w)))
      targetZero :=
    continuous_standardEtaleLocalizationEquation P |>.comp_continuousOn hinv
  have hopenNe : IsOpen {x : ℂ | x ≠ 0} :=
    isOpen_ne_fun continuous_id continuous_const
  change IsOpen (targetZero ∩
    (fun w ↦ standardEtaleLocalizationEquation P (T.symm (zeroSection w))) ⁻¹' {x | x ≠ 0})
  exact hloc.isOpen_inter_preimage htargetZero hopenNe

/-- The inverse of the standard étale chart on its target. It is assigned the center point
outside the target because `OpenPartialHomeomorph` stores total functions. -/
noncomputable def standardEtaleChartInverse (z : standardEtaleCoordinateSpace P)
    (w : Fin n → ℂ) : standardEtaleCoordinateSpace P := by
  classical
  exact if hw : w ∈ standardEtaleChartTarget P z then
    ⟨(standardEtaleImplicitOpenPartialHomeomorph P z).symm (0, w), by
      have heq := congrArg Prod.fst
        ((standardEtaleImplicitOpenPartialHomeomorph P z).right_inv hw.1)
      constructor
      · simpa only [standardEtaleEquation,
          standardEtaleImplicitOpenPartialHomeomorph_apply] using heq
      · simpa only [standardEtaleLocalizationEquation] using hw.2⟩
  else z

@[simp]
lemma standardEtaleChartInverse_of_mem (z : standardEtaleCoordinateSpace P)
    {w : Fin n → ℂ} (hw : w ∈ standardEtaleChartTarget P z) :
    (standardEtaleChartInverse P z w).1 =
      (standardEtaleImplicitOpenPartialHomeomorph P z).symm (0, w) := by
  classical
  simp [standardEtaleChartInverse, hw]

lemma standardEtale_base_mem_chartTarget (z x : standardEtaleCoordinateSpace P)
    (hx : x ∈ standardEtaleChartSource P z) :
    x.1.1 ∈ standardEtaleChartTarget P z := by
  let T := standardEtaleImplicitOpenPartialHomeomorph P z
  have hmap : T x.1 ∈ T.target := T.map_source hx
  have hTx : T x.1 = (0, x.1.1) := by
    rw [standardEtaleImplicitOpenPartialHomeomorph_apply]
    exact Prod.ext (by simpa [standardEtaleEquation] using x.2.1) rfl
  constructor
  · rwa [← hTx]
  · have hinv : T.symm (0, x.1.1) = x.1 := by
      rw [← hTx]
      exact T.left_inv hx
    change standardEtaleLocalizationEquation P (T.symm (0, x.1.1)) ≠ 0
    rw [hinv]
    simpa only [standardEtaleLocalizationEquation] using x.2.2

lemma standardEtaleChartInverse_base (z : standardEtaleCoordinateSpace P)
    {w : Fin n → ℂ} (hw : w ∈ standardEtaleChartTarget P z) :
    (standardEtaleChartInverse P z w).1.1 = w := by
  have hright := congrArg Prod.snd
    ((standardEtaleImplicitOpenPartialHomeomorph P z).right_inv hw.1)
  rw [standardEtaleChartInverse_of_mem P z hw]
  simpa only [standardEtaleImplicitOpenPartialHomeomorph_apply] using hright

lemma standardEtaleChartInverse_left (z x : standardEtaleCoordinateSpace P)
    (hx : x ∈ standardEtaleChartSource P z) :
    standardEtaleChartInverse P z x.1.1 = x := by
  apply Subtype.ext
  rw [standardEtaleChartInverse_of_mem P z (standardEtale_base_mem_chartTarget P z x hx)]
  have hTx : (standardEtaleImplicitOpenPartialHomeomorph P z) x.1 = (0, x.1.1) := by
    rw [standardEtaleImplicitOpenPartialHomeomorph_apply]
    exact Prod.ext (by simpa [standardEtaleEquation] using x.2.1) rfl
  rw [← hTx]
  exact (standardEtaleImplicitOpenPartialHomeomorph P z).left_inv hx

lemma continuousOn_standardEtaleChartInverse (z : standardEtaleCoordinateSpace P) :
    ContinuousOn (standardEtaleChartInverse P z) (standardEtaleChartTarget P z) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let T := standardEtaleImplicitOpenPartialHomeomorph P z
  have hzero : Continuous (fun w : standardEtaleChartTarget P z ↦ ((0 : ℂ), w.1)) :=
    continuous_const.prodMk continuous_subtype_val
  have hzeroTarget : ∀ w : standardEtaleChartTarget P z, (0, w.1) ∈ T.target :=
    fun w ↦ w.2.1
  have hzeroRestrict : Continuous (fun w : standardEtaleChartTarget P z ↦
      (⟨(0, w.1), hzeroTarget w⟩ : T.target)) :=
    hzero.subtype_mk hzeroTarget
  have hTinv : Continuous (T.target.domRestrict T.symm) :=
    continuousOn_iff_continuous_domRestrict.mp T.continuousOn_invFun
  have hambient : Continuous (fun w : standardEtaleChartTarget P z ↦ T.symm (0, w.1)) :=
    hTinv.comp hzeroRestrict
  have hcoordinate : Continuous (fun w : standardEtaleChartTarget P z ↦
      (⟨T.symm (0, w.1), by
        have heq := congrArg Prod.fst (T.right_inv w.2.1)
        constructor
        · simpa [T, standardEtaleEquation] using heq
        · simpa [standardEtaleLocalizationEquation] using w.2.2⟩ :
        standardEtaleCoordinateSpace P)) :=
    hambient.subtype_mk _
  convert hcoordinate using 1
  exact funext fun w ↦ Subtype.ext (standardEtaleChartInverse_of_mem P z w.2)

/-- The ambient inverse of a standard étale projection chart is analytic at every point of its
target. The derivative of the implicit-function homeomorphism is invertible there because every
point of a standard étale equation locus has nonzero distinguished derivative. -/
lemma analyticAt_standardEtaleImplicitOpenPartialHomeomorph_symm_zero
    (z : standardEtaleCoordinateSpace P) {w : Fin n → ℂ}
    (hw : w ∈ standardEtaleChartTarget P z) :
    AnalyticAt ℂ (standardEtaleImplicitOpenPartialHomeomorph P z).symm (0, w) := by
  let T := standardEtaleImplicitOpenPartialHomeomorph P z
  let q : standardEtaleCoordinateSpace P := standardEtaleChartInverse P z w
  have hqval : q.1 = T.symm (0, w) := standardEtaleChartInverse_of_mem P z hw
  let cdf := contDiffAt_standardEtaleEquation P q.1
  let hs := cdf.hasStrictFDerivAt (by simp)
  let φ := hs.implicitFunctionDataOfProdDomain (standardEtale_partial_isInvertible P q)
  let e : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (ℂ × (Fin n → ℂ)) :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hleft : φ.leftFun = standardEtaleEquation P := by
    simpa only [φ] using
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain hs
        (standardEtale_partial_isInvertible P q)
  have hright : φ.rightFun = Prod.fst := by
    simpa only [φ] using
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain hs
        (standardEtale_partial_isInvertible P q)
  have hfun : (T : ((Fin n → ℂ) × ℂ) → (ℂ × (Fin n → ℂ))) = φ.prodFun := by
    funext u
    rw [ImplicitFunctionData.prodFun_apply]
    rw [hleft, hright]
    exact standardEtaleImplicitOpenPartialHomeomorph_apply P z u
  have hderiv : fderiv ℂ (T : ((Fin n → ℂ) × ℂ) → (ℂ × (Fin n → ℂ)))
      (T.symm (0, w)) = (e : ((Fin n → ℂ) × ℂ) →L[ℂ] (ℂ × (Fin n → ℂ))) := by
    rw [hfun, ← hqval]
    simpa only [e, φ, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain] using
      φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  apply T.analyticAt_symm hw.1
  · rw [← hqval]
    have hTformula :
        (T : ((Fin n → ℂ) × ℂ) → (ℂ × (Fin n → ℂ))) =
          fun u ↦ (standardEtaleEquation P u, u.1) := by
      funext u
      exact standardEtaleImplicitOpenPartialHomeomorph_apply P z u
    rw [hTformula]
    exact (analyticAt_standardEtaleEquation P q.1).prod
      (ContinuousLinearMap.analyticAt (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ) q.1)
  · exact hderiv

/-- In ambient coordinates, the inverse branch of a standard étale projection chart is complex
analytic throughout its target. -/
lemma analyticAt_standardEtaleChartInverse_val
    (z : standardEtaleCoordinateSpace P) {w : Fin n → ℂ}
    (hw : w ∈ standardEtaleChartTarget P z) :
    AnalyticAt ℂ (fun v ↦ (standardEtaleChartInverse P z v).1) w := by
  let T := standardEtaleImplicitOpenPartialHomeomorph P z
  have hT : AnalyticAt ℂ T.symm (0, w) :=
    analyticAt_standardEtaleImplicitOpenPartialHomeomorph_symm_zero P z hw
  have hzero : AnalyticAt ℂ (fun v : Fin n → ℂ ↦ ((0 : ℂ), v)) w := by fun_prop
  apply (hT.comp hzero).congr
  filter_upwards [(isOpen_standardEtaleChartTarget P z).eventually_mem hw] with v hv
  exact (standardEtaleChartInverse_of_mem P z hv).symm

/-- In ambient coordinates, the inverse branch of a standard étale projection chart is
holomorphic throughout its target. -/
lemma contDiffOn_standardEtaleChartInverse_val
    (z : standardEtaleCoordinateSpace P) :
    ContDiffOn ℂ ω (fun v ↦ (standardEtaleChartInverse P z v).1)
      (standardEtaleChartTarget P z) :=
  fun _ hw ↦ (analyticAt_standardEtaleChartInverse_val P z hw).contDiffAt.contDiffWithinAt

/-- Evaluation of a quotient representative in ordinary coordinates agrees with the explicit
bivariate polynomial formula. -/
lemma standardEtaleCoordinateHomeomorph_symm_mk
    (z : standardEtaleCoordinateSpace P) (q : (complexPolynomialRing n)[X][X]) :
    (standardEtaleCoordinateHomeomorph P).symm z (Ideal.Quotient.mk _ q) =
      standardEtaleBivariateEvaluation P q z.1 := by
  change standardEtalePointToAlgHom P
      ((standardEtalePointCoordinateHomeomorph P).symm z) (Ideal.Quotient.mk _ q) = _
  rw [standardEtalePointToAlgHom_mk]
  congr 1

/-- Every regular function on a standard étale algebra is analytic in each projection chart. -/
lemma analyticAt_standardEtaleCoordinateEvaluation_chart
    (z : standardEtaleCoordinateSpace P) {w : Fin n → ℂ}
    (hw : w ∈ standardEtaleChartTarget P z) (r : P.Ring) :
    AnalyticAt ℂ
      (fun v ↦ (standardEtaleCoordinateHomeomorph P).symm
        (standardEtaleChartInverse P z v) r) w := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [show (fun v ↦ (standardEtaleCoordinateHomeomorph P).symm
      (standardEtaleChartInverse P z v) (Ideal.Quotient.mk _ q)) =
      fun v ↦ standardEtaleBivariateEvaluation P q
        (standardEtaleChartInverse P z v).1 by
    funext v
    exact standardEtaleCoordinateHomeomorph_symm_mk P _ q]
  have hloc : standardEtaleLocalizationEquation P
      (standardEtaleChartInverse P z w).1 ≠ 0 := by
    simpa only [standardEtaleLocalizationEquation] using
      (standardEtaleChartInverse P z w).2.2
  have houter : AnalyticAt ℂ (standardEtaleBivariateEvaluation P q)
      (standardEtaleChartInverse P z w).1 :=
    analyticAt_standardEtaleBivariateEvaluation P q _ hloc
  have hinner : AnalyticAt ℂ
      (fun v ↦ (standardEtaleChartInverse P z v).1) w :=
    analyticAt_standardEtaleChartInverse_val P z hw
  change AnalyticAt ℂ
    (standardEtaleBivariateEvaluation P q ∘
      fun v ↦ (standardEtaleChartInverse P z v).1) w
  exact houter.comp_of_eq hinner rfl

/-- A neighborhood of a standard étale point on which projection to the polynomial-ring
coordinates is a homeomorphism onto an open set. -/
noncomputable def standardEtaleProjectionChart (z : standardEtaleCoordinateSpace P) :
    OpenPartialHomeomorph (standardEtaleCoordinateSpace P) (Fin n → ℂ) where
  toFun x := x.1.1
  invFun := standardEtaleChartInverse P z
  source := standardEtaleChartSource P z
  target := standardEtaleChartTarget P z
  map_source' x hx := standardEtale_base_mem_chartTarget P z x hx
  map_target' w hw := by
    change (standardEtaleChartInverse P z w).1 ∈
      (standardEtaleImplicitOpenPartialHomeomorph P z).source
    rw [standardEtaleChartInverse_of_mem P z hw]
    exact (standardEtaleImplicitOpenPartialHomeomorph P z).map_target hw.1
  left_inv' x hx := standardEtaleChartInverse_left P z x hx
  right_inv' w hw := standardEtaleChartInverse_base P z hw
  continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := continuousOn_standardEtaleChartInverse P z
  open_source := isOpen_standardEtaleChartSource P z
  open_target := isOpen_standardEtaleChartTarget P z

@[simp]
lemma standardEtaleProjectionChart_symm_apply
    (z : standardEtaleCoordinateSpace P) (w : Fin n → ℂ) :
    (standardEtaleProjectionChart P z).symm w = standardEtaleChartInverse P z w :=
  rfl

/-- A projection chart on the complex algebra homomorphisms of a standard étale algebra. -/
noncomputable def standardEtaleAlgHomProjectionChart (u : P.Ring →ₐ[ℂ] ℂ) :
    OpenPartialHomeomorph (P.Ring →ₐ[ℂ] ℂ) (Fin n → ℂ) :=
  (standardEtaleCoordinateHomeomorph P).toOpenPartialHomeomorph.trans
    (standardEtaleProjectionChart P (standardEtaleCoordinateHomeomorph P u))

lemma mem_standardEtaleAlgHomProjectionChart_source (u : P.Ring →ₐ[ℂ] ℂ) :
    u ∈ (standardEtaleAlgHomProjectionChart P u).source := by
  rw [standardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.trans_source]
  constructor
  · simp
  · change standardEtaleCoordinateHomeomorph P u ∈
      (standardEtaleProjectionChart P (standardEtaleCoordinateHomeomorph P u)).source
    exact standardEtale_mem_implicit_source P (standardEtaleCoordinateHomeomorph P u)

lemma standardEtaleAlgHomProjectionChart_apply (u v : P.Ring →ₐ[ℂ] ℂ) :
    standardEtaleAlgHomProjectionChart P u v =
      mvPolynomialAlgHomHomeomorph n
        (v.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) P.Ring)) := by
  funext i
  rfl

/-- Every regular function is analytic on the inverse of a standard étale algebra-homomorphism
projection chart. -/
lemma analyticAt_standardEtaleAlgHomProjectionChart_symm_apply
    (u : P.Ring →ₐ[ℂ] ℂ) {w : Fin n → ℂ}
    (hw : w ∈ (standardEtaleAlgHomProjectionChart P u).target) (r : P.Ring) :
    AnalyticAt ℂ
      (fun v ↦ (standardEtaleAlgHomProjectionChart P u).symm v r) w := by
  have hw' : w ∈ standardEtaleChartTarget P (standardEtaleCoordinateHomeomorph P u) := by
    rw [standardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.trans_target] at hw
    exact hw.1
  simpa only [standardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    standardEtaleProjectionChart_symm_apply] using
    analyticAt_standardEtaleCoordinateEvaluation_chart P
      (standardEtaleCoordinateHomeomorph P u) hw' r

/-- Projection from a standard étale equation locus to its polynomial coordinates is a local
homeomorphism. -/
lemma isLocalHomeomorph_standardEtaleCoordinateProjection :
    IsLocalHomeomorph (fun z : standardEtaleCoordinateSpace P ↦ z.1.1) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact IsLocalHomeomorphOn.mk _ _ fun z _ ↦
    ⟨standardEtaleProjectionChart P z, standardEtale_mem_implicit_source P z, fun _ _ ↦ rfl⟩

/-- Restriction of a complex point of a standard étale algebra to the polynomial base. -/
def standardEtaleBaseAlgHom (u : P.Ring →ₐ[ℂ] ℂ) : complexPolynomialRing n →ₐ[ℂ] ℂ :=
  u.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) P.Ring)

/-- On complex algebra homomorphisms, a standard étale algebra is locally homeomorphic to its
polynomial base by restriction. -/
lemma isLocalHomeomorph_standardEtaleBaseAlgHom :
    IsLocalHomeomorph (standardEtaleBaseAlgHom P) := by
  have hcoordinates := (isLocalHomeomorph_standardEtaleCoordinateProjection P).comp
    (standardEtaleCoordinateHomeomorph P).isLocalHomeomorph
  have h := (mvPolynomialAlgHomHomeomorph n).symm.isLocalHomeomorph.comp hcoordinates
  convert h using 1
  exact funext fun _ ↦ ((mvPolynomialAlgHomHomeomorph n).symm_apply_apply _).symm

variable (S : Type) [CommRing S] [Algebra ℂ S]
  [Algebra (complexPolynomialRing n) S]
  [IsScalarTower ℂ (complexPolynomialRing n) S]
  [Algebra.IsStandardEtale (complexPolynomialRing n) S]

/-- A chosen standard étale presentation of a standard étale algebra. -/
def chosenStandardEtalePresentation :
    StandardEtalePresentation (complexPolynomialRing n) S :=
  Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some

/-- The standard étale pair in the chosen presentation. -/
abbrev chosenStandardEtalePair : StandardEtalePair (complexPolynomialRing n) :=
  (chosenStandardEtalePresentation (n := n) S).P

/-- The chosen presentation is also an equivalence of complex algebras. -/
def standardEtalePresentationComplexAlgEquiv :
    S ≃ₐ[ℂ] (chosenStandardEtalePair (n := n) S).Ring :=
  (chosenStandardEtalePresentation (n := n) S).equivRing.restrictScalars ℂ

/-- Restriction of a complex point of a standard étale algebra to its polynomial base. -/
def isStandardEtaleBaseAlgHom (u : S →ₐ[ℂ] ℂ) :
    complexPolynomialRing n →ₐ[ℂ] ℂ :=
  u.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) S)

/-- A projection chart for an arbitrary standard étale algebra, transported through its chosen
standard étale presentation. -/
noncomputable def isStandardEtaleAlgHomProjectionChart (u : S →ₐ[ℂ] ℂ) :
    OpenPartialHomeomorph (S →ₐ[ℂ] ℂ) (Fin n → ℂ) :=
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := chosenStandardEtalePair (n := n) S
  let q := (precompAlgEquivHomeomorph e).symm u
  (precompAlgEquivHomeomorph e).symm.toOpenPartialHomeomorph.trans
    (standardEtaleAlgHomProjectionChart Q q)

lemma mem_isStandardEtaleAlgHomProjectionChart_source (u : S →ₐ[ℂ] ℂ) :
    u ∈ (isStandardEtaleAlgHomProjectionChart (n := n) S u).source := by
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := chosenStandardEtalePair (n := n) S
  let q := (precompAlgEquivHomeomorph e).symm u
  rw [isStandardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.trans_source]
  constructor
  · simp
  · change q ∈ (standardEtaleAlgHomProjectionChart Q q).source
    exact mem_standardEtaleAlgHomProjectionChart_source Q q

lemma isStandardEtaleAlgHomProjectionChart_apply (u v : S →ₐ[ℂ] ℂ) :
    isStandardEtaleAlgHomProjectionChart (n := n) S u v =
      mvPolynomialAlgHomHomeomorph n (isStandardEtaleBaseAlgHom (n := n) S v) := by
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := chosenStandardEtalePair (n := n) S
  let q := (precompAlgEquivHomeomorph e).symm u
  rw [isStandardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.trans_apply,
    standardEtaleAlgHomProjectionChart_apply]
  apply congrArg (mvPolynomialAlgHomHomeomorph n)
  apply AlgHom.ext
  intro b
  change v (e.symm (algebraMap (complexPolynomialRing n) Q.Ring b)) =
    v (algebraMap (complexPolynomialRing n) S b)
  congr 1
  have hb := (chosenStandardEtalePresentation (n := n) S).equivRing.commutes b
  change e (algebraMap (complexPolynomialRing n) S b) =
    algebraMap (complexPolynomialRing n) Q.Ring b at hb
  rw [← hb, e.symm_apply_apply]

/-- Regular functions are analytic on inverses of the transported standard étale projection
charts. -/
lemma analyticAt_isStandardEtaleAlgHomProjectionChart_symm_apply
    (u : S →ₐ[ℂ] ℂ) {w : Fin n → ℂ}
    (hw : w ∈ (isStandardEtaleAlgHomProjectionChart (n := n) S u).target) (r : S) :
    AnalyticAt ℂ
      (fun v ↦ (isStandardEtaleAlgHomProjectionChart (n := n) S u).symm v r) w := by
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := chosenStandardEtalePair (n := n) S
  let q := (precompAlgEquivHomeomorph e).symm u
  have hw' : w ∈ (standardEtaleAlgHomProjectionChart Q q).target := by
    rw [isStandardEtaleAlgHomProjectionChart, OpenPartialHomeomorph.trans_target] at hw
    exact hw.1
  exact (analyticAt_standardEtaleAlgHomProjectionChart_symm_apply Q q hw' (e r)).congr
    (.of_forall fun _ ↦ rfl)

/-- Restriction to the polynomial base is a local homeomorphism for every standard étale
algebra. -/
lemma isLocalHomeomorph_isStandardEtaleBaseAlgHom :
    IsLocalHomeomorph (isStandardEtaleBaseAlgHom (n := n) S) := by
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := chosenStandardEtalePair (n := n) S
  have h := (isLocalHomeomorph_standardEtaleBaseAlgHom Q).comp
    (precompAlgEquivHomeomorph e).symm.isLocalHomeomorph
  convert h using 1
  funext u
  apply AlgHom.ext
  intro b
  change u (algebraMap (complexPolynomialRing n) S b) =
    u (e.symm (algebraMap (complexPolynomialRing n) Q.Ring b))
  congr 1
  have hb := (chosenStandardEtalePresentation (n := n) S).equivRing.commutes b
  change e (algebraMap (complexPolynomialRing n) S b) =
    algebraMap (complexPolynomialRing n) Q.Ring b at hb
  rw [← hb, e.symm_apply_apply]

variable {S}

variable (T : Type) [CommRing T] [Algebra ℂ T]
  [Algebra (complexPolynomialRing n) T]
  [IsScalarTower ℂ (complexPolynomialRing n) T]

/-- Restriction of a complex point of an algebra over a polynomial ring to the polynomial
base. -/
def etaleBaseAlgHom (u : T →ₐ[ℂ] ℂ) : complexPolynomialRing n →ₐ[ℂ] ℂ :=
  u.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) T)

variable [Algebra.Etale (complexPolynomialRing n) T]

/-- Restriction to the polynomial base is a local homeomorphism for every étale algebra. The
proof localizes at the kernel of each complex point and uses Mathlib's standard étale local
presentation theorem. -/
lemma isLocalHomeomorph_etaleBaseAlgHom :
    IsLocalHomeomorph (etaleBaseAlgHom (n := n) T) := by
  intro u
  let Q : Ideal T := RingHom.ker u.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime u.toRingHom
  let : Algebra.IsEtaleAt (complexPolynomialRing n) Q := by
    have : Algebra.FormallyEtale T (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_isLocalization Q.primeCompl
    exact Algebra.FormallyEtale.comp (complexPolynomialRing n) T (Localization.AtPrime Q)
  obtain ⟨f, hfQ, hfstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := complexPolynomialRing n) Q
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away f) := hfstd
  have hfu : u f ≠ 0 := by
    simpa [Q, RingHom.mem_ker] using hfQ
  let j := localizationAwayAlgHomMap T f
  let F := etaleBaseAlgHom (n := n) T
  let G := isStandardEtaleBaseAlgHom (n := n) (Localization.Away f)
  have hj : IsLocalHomeomorph j := isLocalHomeomorph_localizationAwayAlgHomMap T f
  have hG : IsLocalHomeomorph G :=
    isLocalHomeomorph_isStandardEtaleBaseAlgHom (n := n) (Localization.Away f)
  have hcomp : G = F ∘ j := funext fun _ ↦ AlgHom.ext fun _ ↦ rfl
  have hFG : IsLocalHomeomorph (F ∘ j) := hcomp ▸ hG
  have hFonImage : IsLocalHomeomorphOn F (j '' Set.univ) :=
    hFG.isLocalHomeomorphOn.of_comp_right (s := Set.univ) hj.isLocalHomeomorphOn
  have hFon : IsLocalHomeomorphOn F (Set.range j) := by
    simpa only [Set.image_univ] using hFonImage
  have hu : u ∈ Set.range j := by
    let v := (localizationAwayAlgHomHomeomorph T f).symm ⟨u, hfu⟩
    refine ⟨v, ?_⟩
    change ((localizationAwayAlgHomHomeomorph T f) v).1 = u
    rw [Homeomorph.apply_symm_apply]
  exact hFon u hu

/-- Standard étale localization data at a complex point of an étale algebra. -/
structure EtaleStandardNeighborhood (u : T →ₐ[ℂ] ℂ) where
  /-- An element not vanishing at the chosen point. -/
  element : T
  /-- The chosen element does not vanish at the point. -/
  nonzero : u element ≠ 0
  /-- Localizing at the chosen element gives a standard étale algebra. -/
  isStandard : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away element)

omit [IsScalarTower ℂ (complexPolynomialRing n) T] in
/-- Étaleness supplies a standard étale localization at every complex point. -/
lemma nonempty_etaleStandardNeighborhood (u : T →ₐ[ℂ] ℂ) :
    Nonempty (EtaleStandardNeighborhood (n := n) T u) := by
  let Q : Ideal T := RingHom.ker u.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime u.toRingHom
  let : Algebra.IsEtaleAt (complexPolynomialRing n) Q := by
    have : Algebra.FormallyEtale T (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_isLocalization Q.primeCompl
    exact Algebra.FormallyEtale.comp (complexPolynomialRing n) T (Localization.AtPrime Q)
  obtain ⟨f, hfQ, hfstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := complexPolynomialRing n) Q
  refine ⟨⟨f, ?_, hfstd⟩⟩
  simpa [Q, RingHom.mem_ker] using hfQ

/-- A chosen standard étale localization at a complex point of an étale algebra. -/
noncomputable def etaleStandardNeighborhood (u : T →ₐ[ℂ] ℂ) :
    EtaleStandardNeighborhood (n := n) T u :=
  Classical.choice (nonempty_etaleStandardNeighborhood (n := n) T u)

/-- The point of the chosen standard étale localization lying over `u`. -/
noncomputable def pointInEtaleStandardNeighborhood (u : T →ₐ[ℂ] ℂ) :
    Localization.Away (etaleStandardNeighborhood (n := n) T u).element →ₐ[ℂ] ℂ :=
  (localizationAwayAlgHomHomeomorph T
    (etaleStandardNeighborhood (n := n) T u).element).symm
      ⟨u, (etaleStandardNeighborhood (n := n) T u).nonzero⟩

/-- A projection chart on the complex points of an arbitrary étale algebra. It is obtained from a
standard étale chart after restricting to a principal open neighborhood. -/
noncomputable def etaleAlgHomProjectionChart (u : T →ₐ[ℂ] ℂ) :
    OpenPartialHomeomorph (T →ₐ[ℂ] ℂ) (Fin n → ℂ) := by
  let D := etaleStandardNeighborhood (n := n) T u
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away D.element) :=
    D.isStandard
  exact (isStandardEtaleAlgHomProjectionChart (n := n) (Localization.Away D.element)
    (pointInEtaleStandardNeighborhood (n := n) T u)).lift_openEmbedding
      (isOpenEmbedding_localizationAwayAlgHomMap T D.element)

lemma mem_etaleAlgHomProjectionChart_source (u : T →ₐ[ℂ] ℂ) :
    u ∈ (etaleAlgHomProjectionChart (n := n) T u).source := by
  let D := etaleStandardNeighborhood (n := n) T u
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away D.element) :=
    D.isStandard
  let v := pointInEtaleStandardNeighborhood (n := n) T u
  rw [etaleAlgHomProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨v, mem_isStandardEtaleAlgHomProjectionChart_source
    (n := n) (Localization.Away D.element) v, ?_⟩
  change (localizationAwayAlgHomHomeomorph T D.element v).1 = u
  rw [show v = (localizationAwayAlgHomHomeomorph T D.element).symm
    ⟨u, D.nonzero⟩ by rfl, Homeomorph.apply_symm_apply]

lemma etaleAlgHomProjectionChart_apply_of_mem (u v : T →ₐ[ℂ] ℂ)
    (hv : v ∈ (etaleAlgHomProjectionChart (n := n) T u).source) :
    etaleAlgHomProjectionChart (n := n) T u v =
      mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) T v) := by
  let D := etaleStandardNeighborhood (n := n) T u
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away D.element) :=
    D.isStandard
  rw [etaleAlgHomProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hv
  obtain ⟨q, hq, rfl⟩ := hv
  change ((isStandardEtaleAlgHomProjectionChart (n := n) (Localization.Away D.element)
      (pointInEtaleStandardNeighborhood (n := n) T u)).lift_openEmbedding
        (isOpenEmbedding_localizationAwayAlgHomMap T D.element))
      (localizationAwayAlgHomMap T D.element q) = _
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [isStandardEtaleAlgHomProjectionChart_apply]
  apply congrArg (mvPolynomialAlgHomHomeomorph n)
  apply AlgHom.ext
  intro b
  rfl

/-- Every regular function is analytic on the inverse of the chosen projection chart for an
arbitrary étale algebra. -/
lemma analyticAt_etaleAlgHomProjectionChart_symm_apply
    (u : T →ₐ[ℂ] ℂ) {w : Fin n → ℂ}
    (hw : w ∈ (etaleAlgHomProjectionChart (n := n) T u).target) (r : T) :
    AnalyticAt ℂ (fun v ↦ (etaleAlgHomProjectionChart (n := n) T u).symm v r) w := by
  let D := etaleStandardNeighborhood (n := n) T u
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away D.element) :=
    D.isStandard
  let q := pointInEtaleStandardNeighborhood (n := n) T u
  have hw' : w ∈
      (isStandardEtaleAlgHomProjectionChart (n := n) (Localization.Away D.element) q).target := by
    simpa only [etaleAlgHomProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_target] using hw
  have h := analyticAt_isStandardEtaleAlgHomProjectionChart_symm_apply
    (n := n) (Localization.Away D.element) q hw'
      (algebraMap T (Localization.Away D.element) r)
  exact h.congr (.of_forall fun _ ↦ rfl)

end

end AlgebraicGeometry.ComplexAlgHom

namespace AlgebraicGeometry.ComplexPoint

open ComplexAlgHom Point

noncomputable section

variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- The complex-point map from the spectrum of a polynomial ring to algebraic affine space. -/
def polynomialSpecToAffineSpacePointMap :
    ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n))) →
      ComplexPoint (Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) :=
  map (Over.homMk (AffineSpace.SpecIso (Fin n) ↧ℂ).inv (AffineSpace.SpecIso_inv_over ↧ℂ))

/-- The scheme isomorphism between the spectrum of a polynomial ring and affine space agrees
with evaluation of the polynomial variables. -/
lemma affineSpaceEquiv_polynomialSpecToAffineSpacePointMap
    (z : ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n)))) :
    affineSpaceEquiv (Fin n) (polynomialSpecToAffineSpacePointMap (n := n) z) =
      mvPolynomialAlgHomHomeomorph n (affineSpecEquiv (complexPolynomialRing n) z) := by
  funext i
  change (Scheme.ΓSpecIso ↧ℂ).hom
      (z.left.appTop ((AffineSpace.SpecIso (Fin n) ↧ℂ).inv.appTop
        (AffineSpace.coord (Spec ↧ℂ) i))) =
    affineSpecEquiv (complexPolynomialRing n) z (MvPolynomial.X i)
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  rw [affineSpecEquiv_apply, evaluate_top_eq_appTop]

/-- The affine scheme morphism associated to a standard étale algebra. -/
abbrev standardEtaleSpecMap :
    Spec ↧P.Ring ⟶ Spec ↧(complexPolynomialRing n) :=
  Spec.map (CommRingCat.ofHom (algebraMap (complexPolynomialRing n) P.Ring))

lemma standardEtaleSpecMap_over :
    standardEtaleSpecMap P ≫ affineSpecStructureMap (complexPolynomialRing n) =
      affineSpecStructureMap P.Ring := by
  rw [← Spec.map_comp]
  congr 1

/-- The map on complex points associated to a standard étale algebra. -/
def standardEtaleComplexPointMap :
    ComplexPoint (Over.mk (affineSpecStructureMap P.Ring)) →
      ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n))) :=
  Point.map (Over.homMk (standardEtaleSpecMap P) (standardEtaleSpecMap_over P))

lemma affineSpecEquiv_standardEtaleComplexPointMap
    (z : ComplexPoint (Over.mk (affineSpecStructureMap P.Ring))) :
    affineSpecEquiv (complexPolynomialRing n) (standardEtaleComplexPointMap P z) =
      standardEtaleBaseAlgHom P (affineSpecEquiv P.Ring z) := by
  ext b
  simp [standardEtaleComplexPointMap, Point.map, affineSpecEquiv,
    standardEtaleBaseAlgHom, standardEtaleSpecMap, Spec.preimage_comp]

/-- A standard étale morphism of affine complex schemes is a local homeomorphism on complex
points. -/
lemma isLocalHomeomorph_standardEtaleComplexPointMap :
    @IsLocalHomeomorph
      (ComplexPoint (Over.mk (affineSpecStructureMap P.Ring)))
      (ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n))))
      analyticTopology analyticTopology (standardEtaleComplexPointMap P) := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (affineSpecStructureMap P.Ring))) := analyticTopology
  let : TopologicalSpace
      (ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n)))) := analyticTopology
  have h := (affineSpecHomeomorph (complexPolynomialRing n)).symm.isLocalHomeomorph.comp
    ((isLocalHomeomorph_standardEtaleBaseAlgHom P).comp
      (affineSpecHomeomorph P.Ring).isLocalHomeomorph)
  convert h using 1
  exact funext fun z ↦
    (Homeomorph.eq_symm_apply _).mpr (affineSpecEquiv_standardEtaleComplexPointMap P z)

end

end AlgebraicGeometry.ComplexPoint
