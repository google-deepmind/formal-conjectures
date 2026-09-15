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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentLocalGenerator

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentDimension
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension
import FormalConjecturesForMathlib.Mathlib.Algebra.PolynomialCatenary
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentNormalGeometry
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothCatenaryDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization

/-!
# Dimensions at closed points of cycle components

This file proves that every closed point of the reduced closure of a codimension-`p` point in a
smooth complex `d`-fold has coheight `d - p`.  The commutative-algebra input is the
equidimensionality of a finite-type domain over a field: every maximal ideal has height equal to
the ring's Krull dimension.  We prove it directly from Noether normalization, incomparability,
and going down; no catenarity or equidimensionality assertion is assumed.

The closed-point formula removes the small-dimensional restriction from the separate component
and ambient coordinate package and from the resulting component-local fundamental-class
generator.  The two coordinate systems are still independent: this file does not assert a
simultaneous normal form for the closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory Ideal MvPolynomial Topology TopologicalSpace

namespace Algebra

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

include k

/-- Every maximal ideal of a finite-type domain over a field has height equal to the Krull
dimension of the domain. -/
lemma FiniteType.height_eq_ringKrullDim_of_isMaximal
    (P : Ideal A) [P.IsMaximal] :
    (↑P.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
  let : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (g.commutes r).symm)
  let : Algebra.IsIntegral (MvPolynomial (Fin n) k) A :=
    ⟨hfinite.to_isIntegral⟩
  let : Algebra.HasGoingDown (MvPolynomial (Fin n) k) A := inferInstance
  have hunder : (P.under (MvPolynomial (Fin n) k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hheight : P.height = (P.under (MvPolynomial (Fin n) k)).height := by
    calc
      P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A) :=
        by
          change (⟨P, inferInstance⟩ : PrimeSpectrum A).asIdeal.height =
            Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A)
          exact PrimeSpectrum.height_eq_orderHeight _
      _ = Order.height (PrimeSpectrum.comap
          (algebraMap (MvPolynomial (Fin n) k) A)
          (⟨P, inferInstance⟩ : PrimeSpectrum A)) := by
        apply Order.height_eq_of_strictMono
          (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) k) A))
          (fun _ _ hQQ' ↦ Ideal.IsIntegral.comap_lt_comap hQQ')
        intro Q q hq
        have hq' : q.asIdeal < Q.asIdeal.under (MvPolynomial (Fin n) k) := by
          change q.asIdeal <
            (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) k) A) Q).asIdeal at hq
          simpa only [PrimeSpectrum.comap_asIdeal] using hq
        obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
          Q.asIdeal.exists_ideal_lt_liesOver_of_lt
            (R := MvPolynomial (Fin n) k) (p := q.asIdeal)
              (q := Q.asIdeal.under (MvPolynomial (Fin n) k)) hq'
        refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
        apply PrimeSpectrum.ext
        simpa [Ideal.under] using hQ'over.over.symm
      _ = (P.under (MvPolynomial (Fin n) k)).height := by
        rw [show P.under (MvPolynomial (Fin n) k) =
          (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) k) A)
            (⟨P, inferInstance⟩ : PrimeSpectrum A)).asIdeal from rfl]
        exact (PrimeSpectrum.height_eq_orderHeight _).symm
  rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_fin, hheight,
    MvPolynomial.height_eq_fin_of_isMaximal k n (P.under (MvPolynomial (Fin n) k))]
  norm_num

end Algebra

namespace RingHom

/-- The quotient by a prime of height `p` in a standard-smooth complex algebra of relative
dimension `d` has Krull dimension `d - p`. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_quotient_eq_sub_complex
    {A : Type} [CommRing A] {f : ℂ →+* A} {d p : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d)
    (P : Ideal A) [P.IsPrime] (hP : P.height = p) :
    ringKrullDim (A ⧸ P) = d - p := by
  have hsum := hf.height_add_ringKrullDim_quotient_eq_complex P
  rw [hP] at hsum
  obtain ⟨a, b, ha, hb, hab⟩ := WithBot.add_eq_coe.mp hsum
  have ha' : a = (p : ℕ∞) := WithBot.coe_injective ha
  subst a
  have hbtop : b ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hab
    exact ENat.top_ne_natCast d hab
  lift b to ℕ using hbtop with n
  have hpn : p + n = d := by exact_mod_cast hab
  rw [← hb, WithBot.coe_natCast]
  congr
  lia

end RingHom

namespace AlgebraicGeometry

attribute [local instance] overSpecAlgebra

variable (X : Over (Spec ↧ℂ)) {d p : ℕ}

/-- Every closed point of the reduced closure of a codimension-`p` point in a smooth complex
`d`-fold has coheight `d - p` inside that reduced closure. -/
lemma cycleComponent_closedPoint_coheight_eq_sub
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : cycleComponent X.left x)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) (hz : IsClosed {z}) :
    Order.coheight z = d - p := by
  let c : cycleComponent X.left x ⟶ X.left := cycleComponentι X.left x
  let y : X.left := c z
  have hyx : y ≤ x := (cycleComponentOrderIsoIic X.left x z).2
  obtain ⟨U, hU, hyU, hstandard⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) X.hom y
  have hxU : x ∈ U := by
    rw [Scheme.le_iff_specializes] at hyx
    exact hyx.mem_open U.isOpen hyU
  let W : (cycleComponent X.left x).Opens := c ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage c
  have hzW : z ∈ W := hyU
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let xu : U.toScheme := ⟨x, hxU⟩
  let zw : W.toScheme := ⟨z, hzW⟩
  let q : Γ(X.left, U) →+* Γ(cycleComponent X.left x, W) :=
    (c.app U).hom
  have hqsurj : Function.Surjective q := c.app_surjective U hU
  let P : Ideal Γ(X.left, U) :=
    (hU.primeIdealOf xu).asIdeal
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X.left) ⟨closure {x}, isClosed_closure⟩
  have hsingleton : hU.fromSpec ⁻¹' ({x} : Set X.left) =
      ({hU.primeIdealOf xu} : Set (Spec Γ(X.left, U))) := by
    ext Q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hQ ↦ hU.fromSpec.isOpenEmbedding.injective
      (hQ.trans (hU.fromSpec_primeIdealOf xu).symm), ?_⟩
    rintro rfl
    exact hU.fromSpec_primeIdealOf xu
  have hpreimage : hU.fromSpec ⁻¹' closure {x} =
      closure {hU.primeIdealOf xu} := by
    have hclosure := congrArg
      (fun T : Set (Spec Γ(X.left, U)) ↦ closure T) hsingleton
    exact (hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous ({x} : Set X.left)).trans hclosure
  have hideal : I.ideal ⟨U, hU⟩ = P := by
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure {x}) = P
    erw [hpreimage, PrimeSpectrum.vanishingIdeal_closure,
      PrimeSpectrum.vanishingIdeal_singleton]
  have hqker : RingHom.ker q = P := by
    change RingHom.ker (c.app U).hom = P
    rw [← Scheme.Hom.ker_apply c ⟨U, hU⟩]
    calc
      c.ker.ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ := by
        rw [show c = I.subschemeι from rfl]
        exact congrArg (fun J : X.left.IdealSheafData ↦ J.ideal ⟨U, hU⟩)
          I.ker_subschemeι
      _ = P := hideal
  have hPheight : P.height = p := by
    calc
      P.height = Order.coheight xu := by
        change (hU.primeIdealOf xu).asIdeal.height = Order.coheight xu
        exact hU.primeIdealOf_height_eq_coheight _
      _ = Order.coheight x := by
        have h := coheight_eq_of_isOpenImmersion
          (x := xu) U.ι
        simpa [xu] using h.symm
      _ = p := hx
  have hquotient : ringKrullDim (Γ(X.left, U) ⧸ P) = d - p :=
    (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) X hstandard).ringKrullDim_quotient_eq_sub_complex
        P hPheight
  have hringW : ringKrullDim Γ(cycleComponent X.left x, W) = d - p := by
    calc
      ringKrullDim Γ(cycleComponent X.left x, W) =
          ringKrullDim (Γ(X.left, U) ⧸ RingHom.ker q) :=
        (ringKrullDim_eq_of_ringEquiv
          (RingHom.quotientKerEquivOfSurjective hqsurj)).symm
      _ = ringKrullDim (Γ(X.left, U) ⧸ P) := by rw [hqker]
      _ = d - p := hquotient
  let s : cycleComponent X.left x ⟶ Spec ↧ℂ := c ≫ X.hom
  let : Algebra ℂ Γ(cycleComponent X.left x, W) :=
    overSpecAlgebra (Over.mk s) W
  let : Algebra.FiniteType ℂ Γ(cycleComponent X.left x, W) := by
    rw [← RingHom.finiteType_algebraMap]
    change (algebraMap ℂ Γ(cycleComponent X.left x, W)).FiniteType
    apply (s.finiteType_appLE (isAffineOpen_top (Spec ↧ℂ)) hW (by simp)).comp
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv.surjective
  let Q : Ideal Γ(cycleComponent X.left x, W) :=
    (hW.primeIdealOf zw).asIdeal
  have hQmax : Q.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed
    zw hz
  let : Q.IsMaximal := hQmax
  have hQheight : (↑Q.height : WithBot ℕ∞) = d - p := by
    rw [Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal
      (k := ℂ) Q, hringW]
  have hQcoheight : Q.height = Order.coheight z := by
    calc
      Q.height = Order.coheight zw := by
        change (hW.primeIdealOf zw).asIdeal.height = Order.coheight zw
        exact hW.primeIdealOf_height_eq_coheight _
      _ = Order.coheight z := by
        have h := coheight_eq_of_isOpenImmersion
          (x := zw) W.ι
        simpa [zw] using h.symm
  apply WithBot.coe_injective
  rw [← hQcoheight]
  exact hQheight

/-- The underlying point of every complex point of a codimension-`p` reduced component has
coheight `d - p`. -/
lemma cycleComponent_complexPoint_coheight_eq_sub
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    Order.coheight z.underlying = d - p :=
  cycleComponent_closedPoint_coheight_eq_sub X x z.underlying hx
    (cycleComponent_complexPoint_underlying_isClosed X x z)

/-- In every ambient dimension, a reduced component of coheight `p` has separate component and
ambient étale coordinates, with exactly `d - p` component coordinates. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    Nonempty (CycleComponentSeparateLocalCoordinates X x d (d - p)) := by
  let c : cycleComponent X.left x ⟶ Spec ↧ℂ :=
    cycleComponentι X.left x ≫ X.hom
  let S : (cycleComponent X.left x).Opens := c.smoothLocus
  let g : S.toScheme ⟶ Spec ↧ℂ := S.ι ≫ c
  let : Smooth g := cycleComponent_smoothLocus_smooth X x
  obtain ⟨z, hzsmooth, hzclosed⟩ :=
    exists_cycleComponent_smooth_closed_complexPoint X x
  let zs : S.toScheme := ⟨z.underlying, hzsmooth⟩
  obtain ⟨W, hW, hzsW, hstandard⟩ := Smooth.exists_affine_isStandardSmooth g zs
  have hstandardComplex := algebraMap_isStandardSmooth (Over.mk g) hstandard
  obtain ⟨m, hm⟩ :=
    hstandardComplex.exists_isStandardSmoothOfRelativeDimension
  have hzsClosed : IsClosed {zs} := by
    have hpreimage : S.ι ⁻¹' ({z.underlying} : Set (cycleComponent X.left x)) =
        ({zs} : Set S.toScheme) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    exact hpreimage ▸ hzclosed.preimage S.ι.continuous
  let zw : W.toScheme := ⟨zs, hzsW⟩
  let P : Ideal Γ(S, W) := (hW.primeIdealOf zw).asIdeal
  let : P.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed zw hzsClosed
  have hPm : P.height = m :=
    RingHom.IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal hm P
  have hPcoheight : P.height = Order.coheight zw :=
    hW.primeIdealOf_height_eq_coheight zw
  have hWcoheight : Order.coheight zs = Order.coheight zw :=
    coheight_eq_of_isOpenImmersion (x := zw) W.ι
  have hScoheight : Order.coheight z.underlying = Order.coheight zs :=
    coheight_eq_of_isOpenImmersion (x := zs) S.ι
  have hmEq : m = d - p := by
    exact_mod_cast calc
      (m : ℕ∞) = P.height := hPm.symm
      _ = Order.coheight zw := hPcoheight
      _ = Order.coheight zs := hWcoheight.symm
      _ = Order.coheight z.underlying := hScoheight.symm
      _ = d - p := cycleComponent_complexPoint_coheight_eq_sub X x z hx
  subst m
  obtain ⟨coordinateRingHom, hcomp, hetale⟩ := hm.exists_etale_mvPolynomial
  exact ⟨
    { point := z
      point_mem_smoothLocus := hzsmooth
      point_isClosed := hzclosed
      componentNeighborhood := W
      componentNeighborhood_isAffine := hW
      point_mem_componentNeighborhood := hzsW
      componentCoordinateAlgHom :=
        { toRingHom := coordinateRingHom
          commutes' := fun c ↦ DFunLike.congr_fun hcomp c }
      componentCoordinateAlgHom_etale := hetale
      ambientCoordinates := localEtaleCoordinates X d
        (cycleComponentι X.left x z.underlying) }⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

variable (X : Over (Spec ↧ℂ))

/-- In every ambient dimension, exact component coordinates give a transported generator of the
full local homology at the selected smooth component point. -/
lemma exists_span_neighborhoodLocalClass_eq_top
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d (d - p),
      Submodule.span ℚ {C.neighborhoodLocalClass} = ⊤ := by
  obtain ⟨C⟩ := AlgebraicGeometry.nonempty_cycleComponentSeparateLocalCoordinates
    X x d p hx
  exact ⟨C, C.span_neighborhoodLocalClass_eq_top⟩

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
