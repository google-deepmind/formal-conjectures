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

public import FormalConjecturesForMathlib.AlgebraicGeometry.AlgebraicCycleSupport
public import FormalConjecturesForMathlib.RingTheory.TranscendenceDegreeKrullDimension

import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentDimension
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothComplexCoordinates
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothDimensionFormula
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothPointwiseDimension
import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import FormalConjecturesForMathlib.Algebra.PolynomialCatenary
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Catenary dimension formulas for smooth complex schemes

This file proves the arbitrary-dimensional pointwise dimension formula for smooth complex
schemes.  Its commutative-algebra bridge is
`FormalConjecturesForMathlib.RingTheory.TranscendenceDegreeKrullDimension`, which compares quotient
dimensions under a quasi-finite map of finite-type algebras using Noether normalization and the
finite extension of residue fields, rather than any unproved catenarity assumption or flatness
of the quotient map.

Applied to the étale polynomial coordinates of a standard-smooth algebra, the bridge transfers
the arbitrary-prime polynomial dimension formula.  An affine neighborhood then supplies enough
specialization chains to prove `height x + coheight x = d` at every point of a smooth complex
`d`-fold.  Consequently, the reduced closure of a point of coheight `p` has dimension `d - p`.
-/

@[expose] public noncomputable section

open CategoryTheory Ideal MvPolynomial Topology

namespace AlgebraicGeometry

/-- The dimension of the quotient by the prime represented by a point of an affine spectrum is
at most the order-theoretic height of that point. -/
lemma ringKrullDim_quotient_le_height_spec {S : Type*} [CommRing S]
    (x : Spec ↧S) :
    ringKrullDim (S ⧸ x.asIdeal) ≤
      (↑(Order.height x) : WithBot ℕ∞) := by
  let e := specOrderIsoPrimeSpectrum ↧S
  let g : (PrimeSpectrum (S ⧸ x.asIdeal))ᵒᵈ → Set.Iic x := fun Q ↦
    ⟨e.symm (OrderDual.toDual
      (PrimeSpectrum.comap (Ideal.Quotient.mk x.asIdeal) Q.ofDual)), by
      apply e.le_iff_le.mp
      change x.asIdeal ≤
        (PrimeSpectrum.comap (Ideal.Quotient.mk x.asIdeal) Q.ofDual).asIdeal
      rw [PrimeSpectrum.comap_asIdeal]
      intro a ha
      rw [Ideal.mem_comap]
      have hz : Ideal.Quotient.mk x.asIdeal a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [hz]
      exact (OrderDual.ofDual Q).asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro Q Q' hQQ'
    apply Subtype.mk_lt_mk.mpr
    apply e.symm.strictMono
    exact (RingHom.strictMono_comap_of_surjective
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk x.asIdeal))).dual hQQ'
  calc
    ringKrullDim (S ⧸ x.asIdeal) =
        Order.krullDim (PrimeSpectrum (S ⧸ x.asIdeal)) := rfl
    _ = Order.krullDim ((PrimeSpectrum (S ⧸ x.asIdeal))ᵒᵈ) :=
      Order.krullDim_orderDual.symm
    _ ≤ Order.krullDim (Set.Iic x) := Order.krullDim_le_of_strictMono g hg
    _ = (↑(Order.height x) : WithBot ℕ∞) := (Order.height_eq_krullDim_Iic x).symm

/-- An inducing map between schemes is strictly monotone for their specialization orders. -/
private lemma Scheme.Hom.strictMono_base_of_isInducing {X Y : Scheme.{0}}
    (f : X ⟶ Y) (hf : IsInducing f.base) : StrictMono f.base := by
  intro x y hxy
  rw [lt_iff_le_not_ge] at hxy ⊢
  constructor
  · rw [Scheme.le_iff_specializes, hf.specializes_iff,
      ← Scheme.le_iff_specializes]
    exact hxy.1
  · intro hyx
    apply hxy.2
    rw [Scheme.le_iff_specializes, hf.specializes_iff,
      ← Scheme.le_iff_specializes] at hyx
    exact hyx

/-- An affine quotient gives a lower bound for the height of the corresponding point in the
ambient scheme. -/
lemma IsAffineOpen.ringKrullDim_quotient_le_height {X : Scheme.{0}} {U : X.Opens}
    (hU : IsAffineOpen U) (y : U.toScheme) :
    ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf y).asIdeal) ≤
      (↑(Order.height (U.ι.base y)) : WithBot ℕ∞) := by
  let e : U.toScheme ≃o Spec ↧Γ(X, U) :=
    { toEquiv := hU.isoSpec.hom.homeomorph.toEquiv
      map_rel_iff' := by
        intro a b
        rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
        exact hU.isoSpec.hom.homeomorph.isInducing.specializes_iff }
  calc
    ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf y).asIdeal) ≤
        (↑(Order.height (hU.isoSpec.hom.base y)) : WithBot ℕ∞) :=
      ringKrullDim_quotient_le_height_spec (hU.isoSpec.hom.base y)
    _ = (↑(Order.height y) : WithBot ℕ∞) := by
      rw [show hU.isoSpec.hom.base y = e y from rfl,
        Order.height_orderIso]
    _ ≤ (↑(Order.height (U.ι.base y)) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr <| Order.height_le_height_apply_of_strictMono
        U.ι.base (Scheme.Hom.strictMono_base_of_isInducing U.ι
          U.isOpenEmbedding.isInducing) y

end AlgebraicGeometry

namespace RingHom

/-- For every prime of a standard-smooth complex algebra of relative dimension `d`, its height
plus the dimension of its quotient is `d`. -/
lemma IsStandardSmoothOfRelativeDimension.height_add_ringKrullDim_quotient_eq_complex
    {S : Type} [CommRing S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d)
    (P : Ideal S) [P.IsPrime] :
    (↑P.height : WithBot ℕ∞) + ringKrullDim (S ⧸ P) = d := by
  obtain ⟨g, hgC, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra ℂ S := f.toAlgebra
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' hgC.symm
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  let : Algebra.FiniteType ℂ S :=
    Algebra.FiniteType.trans (R := ℂ) (S := MvPolynomial (Fin d) ℂ)
      (A := S) inferInstance inferInstance
  have hheight : P.height = (P.under (MvPolynomial (Fin d) ℂ)).height :=
    Algebra.QuasiFinite.height_eq_height_under P
  have hquot : ringKrullDim (S ⧸ P) =
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P.under (MvPolynomial (Fin d) ℂ)) :=
    Algebra.QuasiFinite.ringKrullDim_quotient_eq
      (k := ℂ) (R := MvPolynomial (Fin d) ℂ) P
  rw [hheight, hquot]
  exact PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin
    (P.under (MvPolynomial (Fin d) ℂ))

end RingHom

namespace AlgebraicGeometry

variable {X : Scheme.{0}} {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- The pointwise dimension formula holds at every point of a smooth complex scheme of relative
dimension `d`. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_complex
    [SmoothOfRelativeDimension d f] (x : X) :
    Order.height x + Order.coheight x = d := by
  apply le_antisymm
    (SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := d) x)
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  let y : U.toScheme := ⟨x, hxU⟩
  let P : Ideal Γ(X, U) := (hU.primeIdealOf y).asIdeal
  have hsum : (↑P.height : WithBot ℕ∞) +
      ringKrullDim (Γ(X, U) ⧸ P) = d :=
    (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) (Over.mk f) hsmooth).height_add_ringKrullDim_quotient_eq_complex P
  have hPheight : P.height = Order.coheight x := by
    calc
      P.height = Order.coheight y := hU.primeIdealOf_height_eq_coheight y
      _ = Order.coheight x := (coheight_eq_of_isOpenImmersion (x := y) U.ι).symm
  have hquot : ringKrullDim (Γ(X, U) ⧸ P) ≤
      (↑(Order.height x) : WithBot ℕ∞) :=
    IsAffineOpen.ringKrullDim_quotient_le_height hU y
  have hlower : (d : WithBot ℕ∞) ≤
      (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) := by
    calc
      (d : WithBot ℕ∞) =
          (↑P.height : WithBot ℕ∞) + ringKrullDim (Γ(X, U) ⧸ P) := hsum.symm
      _ ≤ (↑P.height : WithBot ℕ∞) +
          (↑(Order.height x) : WithBot ℕ∞) := add_le_add le_rfl hquot
      _ = (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) := by
        rw [hPheight, WithBot.coe_add]
        ac_rfl
  exact WithBot.coe_le_coe.mp (by simpa only [WithBot.coe_natCast] using hlower)

/-- On a smooth complex `d`-fold, a point of coheight `p` has height `d - p`. -/
lemma SmoothOfRelativeDimension.height_eq_sub_of_coheight_eq_complex
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ}
    (hx : Order.coheight x = p) :
    Order.height x = ((d - p : ℕ) : ℕ∞) := by
  have hsum := SmoothOfRelativeDimension.height_add_coheight_eq_complex
    (f := f) (d := d) x
  rw [hx] at hsum
  cases hheight : Order.height x with
  | top => simp [hheight] at hsum
  | coe n =>
      rw [hheight] at hsum
      have hnp : n + p = d := by exact_mod_cast hsum
      exact_mod_cast (Nat.eq_sub_of_add_eq hnp)

/-- The reduced closure of a point of coheight `p` in a smooth complex `d`-fold has order Krull
dimension exactly `d - p`. -/
lemma SmoothOfRelativeDimension.orderKrullDim_cycleComponent_eq_sub_complex
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ}
    (hx : Order.coheight x = p) :
    Order.krullDim (cycleComponent X x) =
      (((d - p : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  rw [orderKrullDim_cycleComponent,
    SmoothOfRelativeDimension.height_eq_sub_of_coheight_eq_complex
      (f := f) (d := d) x hx]

/-- The reduced closure of a point of coheight `p` in a smooth complex `d`-fold has topological
Krull dimension exactly `d - p`. -/
lemma SmoothOfRelativeDimension.topologicalKrullDim_cycleComponent_eq_sub_complex
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ}
    (hx : Order.coheight x = p) :
    topologicalKrullDim (cycleComponent X x) =
      (((d - p : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_cycleComponent,
    SmoothOfRelativeDimension.height_eq_sub_of_coheight_eq_complex
      (f := f) (d := d) x hx]

end AlgebraicGeometry
