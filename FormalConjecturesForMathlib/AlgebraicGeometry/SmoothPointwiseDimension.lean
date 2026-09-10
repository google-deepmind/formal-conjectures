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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic

import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentDimension
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothComplexCoordinates
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothDimensionFormula
import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Pointwise dimension of smooth complex schemes

This file proves the pointwise dimension formula at the generic and closed points of an integral
smooth complex scheme.  It also proves the formula at every point in relative dimensions zero,
one, or two.  The proofs pass through affine standard-smooth neighborhoods and maximal ideals
under étale coordinates.

Above relative dimension two, the remaining commutative-algebra statement is the arbitrary-prime
dimension formula for a polynomial ring over a field.  Mathlib currently proves the height of
maximal polynomial ideals and the global Krull dimension, but not this arbitrary-prime catenary
formula.  No higher-dimensional pointwise equality is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace RingHom

/-- Every maximal ideal of a standard-smooth complex algebra of relative dimension `d` has
height `d`. -/
lemma IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal
    {S : Type*} [CommRing S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d) (P : Ideal S) [P.IsMaximal] :
    P.height = d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) ℂ) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hunder : (P.under (MvPolynomial (Fin d) ℂ)).IsMaximal :=
    hfiniteType.isMaximal_comap_of_isJacobsonRing P
  rw [Algebra.QuasiFinite.height_eq_height_under (R := MvPolynomial (Fin d) ℂ)]
  exact MvPolynomial.height_eq_fin_of_isMaximal ℂ d
    (P.under (MvPolynomial (Fin d) ℂ))

end RingHom

namespace AlgebraicGeometry

/-- Under an affine presentation, the height of the corresponding prime ideal is the coheight of
the scheme point. -/
lemma IsAffineOpen.primeIdealOf_height_eq_coheight {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U.toScheme) :
    (hU.primeIdealOf x).asIdeal.height = Order.coheight x := by
  change (hU.isoSpec.hom x : Spec ↧Γ(X, U)).asIdeal.height = Order.coheight x
  calc
    (hU.isoSpec.hom x : Spec ↧Γ(X, U)).asIdeal.height =
        Order.coheight (hU.isoSpec.hom x) :=
      idealHeight_eq_coheight ↧Γ(X, U) (hU.isoSpec.hom x)
    _ = Order.coheight x := coheight_eq_of_isOpenImmersion hU.isoSpec.hom

variable {X : Scheme} {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- A nonempty integral smooth complex scheme of relative dimension `d` has global order Krull
dimension exactly `d`. -/
lemma SmoothOfRelativeDimension.orderKrullDim_eq_complex [IsIntegral X]
    [SmoothOfRelativeDimension d f] : Order.krullDim X = d := by
  apply le_antisymm
    (SmoothOfRelativeDimension.orderKrullDim_le_complex (f := f) (d := d))
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hUdim : Order.krullDim U = d := by
    rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU]
    exact (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) (Over.mk f) hsmooth).ringKrullDim_eq_complex
  rw [← hUdim, ← Scheme.topologicalKrullDim_eq_orderKrullDim U.toScheme,
    ← Scheme.topologicalKrullDim_eq_orderKrullDim X]
  exact U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The height of the generic point of an integral smooth complex `d`-fold is `d`. -/
lemma SmoothOfRelativeDimension.height_genericPoint_eq_complex [IsIntegral X]
    [SmoothOfRelativeDimension d f] : Order.height (genericPoint X) = d := by
  change Order.height (⊤ : X) = d
  apply WithBot.coe_eq_coe.mp
  calc
    (↑(Order.height (⊤ : X)) : WithBot ℕ∞) = Order.krullDim X :=
      Order.height_top_eq_krullDim
    _ = d := SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := f) (d := d)
    _ = ↑(d : ℕ∞) := by norm_cast

/-- The pointwise dimension formula holds at the generic point of an integral smooth complex
scheme. -/
lemma SmoothOfRelativeDimension.height_add_coheight_genericPoint [IsIntegral X]
    [SmoothOfRelativeDimension d f] :
    Order.height (genericPoint X) + Order.coheight (genericPoint X) = d := by
  rw [SmoothOfRelativeDimension.height_genericPoint_eq_complex (f := f) (d := d)]
  change d + Order.coheight (⊤ : X) = d
  rw [Order.coheight_top, add_zero]

/-- The pointwise dimension formula holds at every closed point of an integral smooth complex
scheme. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed [IsIntegral X]
    [SmoothOfRelativeDimension d f] (x : X) (hx : IsClosed {x}) :
    Order.height x + Order.coheight x = d := by
  have hmin : IsMin x := by
    intro y hy
    have hy' : y ∈ closure {x} := by
      rwa [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
    rw [hx.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  have hheight : Order.height x = 0 := Order.IsMin.height_eq_zero hmin
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  let y : U.toScheme := ⟨x, hxU⟩
  let P : Ideal Γ(X, U) := (hU.primeIdealOf y).asIdeal
  let : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed y hx
  have hP : P.height = d :=
    (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) (Over.mk f) hsmooth).height_eq_of_isMaximal P
  have hcoheight : Order.coheight x = d := by
    calc
      Order.coheight x = Order.coheight y := coheight_eq_of_isOpenImmersion (x := y) U.ι
      _ = P.height := (hU.primeIdealOf_height_eq_coheight y).symm
      _ = d := hP
  rw [hheight, hcoheight, zero_add]

/-- The pointwise dimension formula holds everywhere on an integral smooth zero-dimensional
complex scheme. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_zero [IsIntegral X]
    [SmoothOfRelativeDimension 0 f] (x : X) :
    Order.height x + Order.coheight x = 0 :=
  le_antisymm
    (SmoothOfRelativeDimension.height_add_coheight_le_complex (f := f) (d := 0) x) bot_le

/-- The pointwise dimension formula holds everywhere on an integral smooth complex curve. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_one [IsIntegral X]
    [SmoothOfRelativeDimension 1 f] (x : X) :
    Order.height x + Order.coheight x = 1 := by
  have hcoheight : Order.coheight x ≤ 1 :=
    SmoothOfRelativeDimension.coheight_le_complex (f := f) (d := 1) x
  obtain hzero | hone := Order.le_one_iff.mp hcoheight
  · have hx : x = genericPoint X :=
      CodimensionCycle.eq_genericPoint_of_coheight_zero x hzero
    subst x
    exact SmoothOfRelativeDimension.height_add_coheight_genericPoint
      (f := f) (d := 1)
  · have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := 1) x
    rw [hone] at hsum ⊢
    have hheight : Order.height x = 0 :=
      Order.lt_one_iff.mp (ENat.add_one_le_natCast_iff.mp hsum)
    rw [hheight, zero_add]

/-- A minimal point of a scheme is a closed point. -/
lemma Scheme.isClosed_singleton_of_isMin (x : X) (hx : IsMin x) : IsClosed {x} := by
  have hclosure : closure {x} = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyx : y ≤ x := by
        rwa [Scheme.le_iff_specializes, specializes_iff_mem_closure]
      apply Set.mem_singleton_iff.mpr
      apply inseparable_iff_eq.mp
      rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
        ← Scheme.le_iff_specializes]
      exact ⟨hx hyx, hyx⟩
    · exact subset_closure
  rw [← hclosure]
  exact isClosed_closure

/-- The pointwise dimension formula holds at a point whose coheight equals the ambient relative
dimension. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_eq_dimension
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X)
    (hx : Order.coheight x = d) :
    Order.height x + Order.coheight x = d := by
  have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
    (f := f) (d := d) x
  rw [hx] at hsum ⊢
  have hheight : Order.height x = 0 :=
    bot_unique ((ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).mp (by simpa using hsum))
  rw [hheight, zero_add]

/-- The pointwise dimension formula holds at a point whose coheight is one less than the ambient
relative dimension. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_succ_eq_dimension
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X) {p : ℕ}
    (hx : Order.coheight x = p) (hd : p + 1 = d) :
    Order.height x + Order.coheight x = d := by
  have hheight_le : Order.height x ≤ 1 := by
    have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := d) x
    rw [hx, ← hd] at hsum
    have hsum' : Order.height x + (p : ℕ∞) ≤ (p : ℕ∞) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsum
    apply (ENat.add_le_add_iff_left (ENat.natCast_ne_top p)).mp
    simpa only [add_comm] using hsum'
  obtain hheight | hheight := Order.le_one_iff.mp hheight_le
  · have hclosed : IsClosed {x} :=
      Scheme.isClosed_singleton_of_isMin x (Order.height_eq_zero.mp hheight)
    have hformula :=
      SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed
        (f := f) (d := d) x hclosed
    rw [hheight, hx, zero_add] at hformula
    have hpd : p = d := by exact_mod_cast hformula
    lia
  · rw [hheight, hx]
    exact_mod_cast (by lia : 1 + p = d)

/-- The pointwise dimension formula holds everywhere on an integral smooth complex surface. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_two [IsIntegral X]
    [SmoothOfRelativeDimension 2 f] (x : X) :
    Order.height x + Order.coheight x = 2 := by
  have hcoheight : Order.coheight x ≤ 2 :=
    SmoothOfRelativeDimension.coheight_le_complex (f := f) (d := 2) x
  have hne : Order.coheight x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hcoheight
  have hnat : (Order.coheight x).toNat ≤ 2 :=
    ENat.toNat_le_of_le_natCast hcoheight
  have hcases : (Order.coheight x).toNat = 0 ∨
      (Order.coheight x).toNat = 1 ∨ (Order.coheight x).toNat = 2 := by
    lia
  rcases hcases with hzero | hone | htwo
  · have hcozero : Order.coheight x = 0 := by
      rw [← ENat.natCast_toNat hne, hzero]
      rfl
    have hx : x = genericPoint X :=
      CodimensionCycle.eq_genericPoint_of_coheight_zero x hcozero
    subst x
    exact SmoothOfRelativeDimension.height_add_coheight_genericPoint
      (f := f) (d := 2)
  · have hcoone : Order.coheight x = 1 := by
      rw [← ENat.natCast_toNat hne, hone]
      norm_num
    have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := 2) x
    rw [hcoone] at hsum ⊢
    have hheight_le : Order.height x ≤ 1 :=
      ENat.lt_two_iff.mp (ENat.add_one_le_natCast_iff.mp hsum)
    obtain hheight | hheight := Order.le_one_iff.mp hheight_le
    · have hclosed : IsClosed {x} :=
        Scheme.isClosed_singleton_of_isMin x (Order.height_eq_zero.mp hheight)
      have hformula :=
        SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed
          (f := f) (d := 2) x hclosed
      rw [hheight, hcoone, zero_add] at hformula
      norm_num at hformula
    · rw [hheight, one_add_one_eq_two]
  · have hcotwo : Order.coheight x = 2 := by
      rw [← ENat.natCast_toNat hne, htwo]
      norm_num
    have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := 2) x
    rw [hcotwo] at hsum ⊢
    have hheight : Order.height x = 0 :=
      bot_unique ((ENat.add_le_add_iff_right (ENat.natCast_ne_top 2)).mp (by simpa using hsum))
    rw [hheight, zero_add]

/-- The pointwise dimension formula holds everywhere in relative dimension at most two. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_le_two [IsIntegral X]
    [SmoothOfRelativeDimension d f] (hd : d ≤ 2) (x : X) :
    Order.height x + Order.coheight x = d := by
  have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 := by lia
  rcases hd_cases with rfl | rfl | rfl
  · exact SmoothOfRelativeDimension.height_add_coheight_eq_zero (f := f) x
  · exact SmoothOfRelativeDimension.height_add_coheight_eq_one (f := f) x
  · exact SmoothOfRelativeDimension.height_add_coheight_eq_two (f := f) x

end AlgebraicGeometry
