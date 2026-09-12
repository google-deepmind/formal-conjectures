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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ChowGroup
public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.IntegralProjectiveVariety
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothLocus
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometric support of algebraic cycles

An algebraic cycle in Mathlib is indexed by the generic points of its irreducible components.
This file constructs the reduced integral closed subscheme attached to such a point and the
corresponding closed subset of complex points. It also constructs the geometric support of a
whole cycle as the union of the closures of the generic points with nonzero coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

/-- The reduced closed subscheme whose underlying space is the closure of `x`. -/
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme

/-- The canonical closed immersion of the reduced closure of `x`. -/
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι

instance (X : Scheme) (x : X) : IsClosedImmersion (cycleComponentι X x) := by
  change IsClosedImmersion
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι)
  infer_instance

instance (X : Scheme) (x : X) : IsReduced (cycleComponent X x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec ↧(Γ(X, U') ⧸ I.ideal U'))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  change (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' closure {x})).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance (X : Scheme) (x : X) : IrreducibleSpace (cycleComponent X x) :=
  Subtype.irreducibleSpace isIrreducible_singleton.closure

instance (X : Scheme) (x : X) : IsIntegral (cycleComponent X x) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

@[simp]
lemma range_cycleComponentι (X : Scheme) (x : X) :
    Set.range (cycleComponentι X x) = closure {x} := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι) = closure {x}
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The kernel of a complex point is the vanishing ideal of the closure of its underlying scheme
point. -/
private lemma complexPoint_ker_eq_vanishingIdeal_closure
    {X : Over (Spec ↧ℂ)}
    (z : ComplexPoint X) :
    z.left.ker = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {z.underlying}, isClosed_closure⟩ := by
  let f : Spec ↧ℂ ⟶ X.left := z.left
  change f.ker = _
  have hrange : Set.range f = {z.underlying} := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      subst s
      rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨IsLocalRing.closedPoint ℂ, rfl⟩
  have h := Scheme.IdealSheafData.map_vanishingIdeal f
    (⊤ : TopologicalSpace.Closeds (Spec ↧ℂ))
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot] at h
  have himage : f '' (↑(⊤ : TopologicalSpace.Closeds (Spec ↧ℂ)) :
      Set (Spec ↧ℂ)) = {z.underlying} := by
    simpa only [TopologicalSpace.Closeds.coe_top, Set.image_univ] using hrange
  rwa [himage] at h

/-- A cycle component of a projective variety is projective over `ℂ`. -/
instance cycleComponent_projective
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsProjective (cycleComponentι X.left x ≫ X.hom) := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  exact ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := cycleComponentι X.left x ≫ P.immersion
      isClosedImmersion := by
        let := P.isClosedImmersion
        infer_instance
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }
  ⟩⟩

/-- A cycle component of a projective complex variety is proper over `ℂ`. -/
noncomputable instance cycleComponent_isProper
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsProper (cycleComponentι X.left x ≫ X.hom) :=
  inferInstance

/-- A cycle component of a projective complex variety is locally of finite presentation over
`ℂ`. -/
noncomputable instance cycleComponent_locallyOfFinitePresentation
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    LocallyOfFinitePresentation (cycleComponentι X.left x ≫ X.hom) :=
  inferInstance

/-- The integral projective variety defined by one generic point of a smooth projective variety. -/
def cycleComponentVariety
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IntegralProjectiveComplexVariety where
  scheme := cycleComponent X.left x
  isIntegral := inferInstance
  structureMap := cycleComponentι X.left x ≫ X.hom
  projective := cycleComponent_projective X x

/-- The complex points supported on the irreducible closed subset with generic point `x`. -/
def cycleComponentSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set (ComplexPoint X) :=
  Point.underlying ⁻¹' closure {x}

/-- The map on complex points induced by the canonical inclusion of a cycle component. -/
def cycleComponentMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) → (ComplexPoint X) :=
  Point.map (Over.homMk (cycleComponentι X.left x) rfl)

/-- The inclusion of a cycle component on complex points, bundled as a continuous map. -/
def cycleComponentContinuousMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    @ContinuousMap
      (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
      (ComplexPoint X) Point.analyticTopology Point.analyticTopology :=
  Point.continuousMap (Over.homMk (cycleComponentι X.left x) rfl)

lemma range_cycleComponentMap_subset
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set.range (cycleComponentMap X x) ⊆ cycleComponentSupport X x := by
  rintro z ⟨w, rfl⟩
  change (cycleComponentι X.left x) w.underlying ∈ closure {x}
  rw [← range_cycleComponentι X.left x]
  exact ⟨w.underlying, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A complex point in the support of a component annihilates the defining ideal of that
component. -/
lemma cycleComponent_vanishingIdeal_le_complexPoint_ker
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z.underlying ∈ closure {x}) :
    (cycleComponentι X.left x).ker ≤ z.left.ker := by
  unfold cycleComponentι
  rw [Scheme.IdealSheafData.ker_subschemeι]
  change Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x}, isClosed_closure⟩ ≤ z.left.ker
  rw [complexPoint_ker_eq_vanishingIdeal_closure z]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure

/-- Lift a complex point in a component support through the reduced closed component. -/
def cycleComponentComplexPointLift
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z ∈ cycleComponentSupport X x) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) :=
  have hz' : z.underlying ∈ closure {x} := hz
  Over.homMk (IsClosedImmersion.lift (cycleComponentι X.left x) z.left
      (cycleComponent_vanishingIdeal_le_complexPoint_ker X x z hz')) (by
    change _ ≫ (cycleComponentι X.left x ≫ X.hom) = 𝟙 _
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
    exact Over.w z)

@[simp]
lemma cycleComponentMap_lift
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z ∈ cycleComponentSupport X x) :
    cycleComponentMap X x (cycleComponentComplexPointLift X x z hz) = z :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac (cycleComponentι X.left x) z.left _)

/-- A closed immersion of a cycle component is injective on complex points. -/
lemma cycleComponentMap_injective
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Function.Injective (cycleComponentMap X x) := fun _ _ hab =>
  Over.OverMorphism.ext ((cancel_mono (cycleComponentι X.left x)).mp
    (congrArg (fun z => z.left) hab))

/-- Map the complex points of a cycle component into its analytic support. -/
def cycleComponentSupportMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) →
      cycleComponentSupport X x :=
  fun z => ⟨cycleComponentMap X x z,
    range_cycleComponentMap_subset X x ⟨z, rfl⟩⟩

/-- Complex points of the reduced component are equivalent to the points in its analytic
support. -/
def cycleComponentPointEquivSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) ≃
      cycleComponentSupport X x :=
  Equiv.ofBijective (cycleComponentSupportMap X x) ⟨
    fun _ _ h => cycleComponentMap_injective X x (congrArg Subtype.val h),
    fun z => ⟨cycleComponentComplexPointLift X x z z.2,
      Subtype.ext (cycleComponentMap_lift X x z z.2)⟩⟩

/-- The analytic complex points in the smooth locus of a reduced cycle component. -/
def cycleComponentSmoothAnalyticLocus
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :=
  Point.overOpen
    (cycleComponentι X.left x ≫ X.hom).smoothLocus

/-- The image in the ambient analytic space of the smooth locus of a cycle component. -/
def cycleComponentSmoothSupport
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) : Set (ComplexPoint X) :=
  cycleComponentMap X x '' cycleComponentSmoothAnalyticLocus X x

/-- The underlying closed support of an algebraic cycle: the union of the closures of all generic
points having nonzero coefficient. -/
def algebraicCycleSupport {R : Type*} [Zero R] (X : Scheme)
    (c : AlgebraicCycle X R) : Set X :=
  ⋃ x ∈ c.support, closure {x}

/-- The complex points lying over the geometric support of an algebraic cycle. -/
def analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : AlgebraicCycle X.left R) : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' algebraicCycleSupport X.left c

/-- The complex points lying over the closed carrier of a principal divisor. -/
def principalDivisorCarrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) : Set (ComplexPoint X) :=
  (@Point.underlying ℂ _ _ X) ⁻¹' Set.range D.inclusion

end AlgebraicGeometry
