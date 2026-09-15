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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.AlgebraicCycleSupport

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothLocus
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometric support of algebraic cycles

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.AlgebraicCycleSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    c.support.Finite := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ

/-- The reduced closure of a point in a projective complex variety is Noetherian.

This is not an instance: the component does not determine the structure morphism carrying the
projectivity hypothesis. -/
theorem cycleComponent_isNoetherian
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsNoetherian (cycleComponent X.left x) :=
  @isNoetherian_of_isProjective (Over.mk (cycleComponentι X.left x ≫ X.hom))
    (cycleComponent_projective X x)

/-- The smooth locus of an integral cycle component is a smooth complex scheme. -/
theorem cycleComponent_smoothLocus_smooth
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Smooth
      ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
        (cycleComponentι X.left x ≫ X.hom)) :=
  (cycleComponentι X.left x ≫ X.hom).smooth_restrict_smoothLocus

/-- Every integral cycle component has a complex point in its smooth locus. The smooth locus is
dense over the perfect field `ℂ`, and a projective complex variety has a closed point there. -/
theorem exists_cycleComponent_smooth_complexPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ∃ z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)),
      z.underlying ∈
        (cycleComponentι X.left x ≫ X.hom).smoothLocus := by
  let f := cycleComponentι X.left x ≫ X.hom
  let : JacobsonSpace (cycleComponent X.left x) :=
    LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty
    f.smoothLocus.2.isLocallyClosed
  let p := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨Over.homMk p.1 p.2, ?_⟩
  have hp := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hp' : p.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hp
  change p.1 (IsLocalRing.closedPoint ℂ) ∈ f.smoothLocus
  rw [hp']
  exact hy

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (Z : TopologicalSpace.Closeds X.left) :
    IsClosed ((@Point.underlying ℂ _ _ X) ⁻¹'
      (Z : Set X.left)) := by
  rw [← isOpen_compl_iff]
  let U : X.left.Opens := ⟨(Z : Set X.left)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  change @IsOpen (ComplexPoint X) Point.analyticTopology
    ((@Point.underlying ℂ _ _ X) ⁻¹' (Z : Set X.left))ᶜ
  rw [show ((@Point.underlying ℂ _ _ X) ⁻¹'
      (Z : Set X.left))ᶜ = Point.overOpen U by
    apply Set.ext
    intro z
    change (¬Point.underlying z ∈ Z) ↔
      Point.underlying z ∈ (Z : Set X.left)ᶜ
    rfl]
  exact Point.isOpen_overOpen (X := X) U

lemma isClosed_cycleComponentSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsClosed (cycleComponentSupport X x) :=
  isClosed_complexPoint_underlying_preimage X
    ⟨closure {x}, isClosed_closure⟩

/-- The complex points of a reduced cycle component map onto exactly its closed analytic
support. -/
lemma range_cycleComponentMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set.range (cycleComponentMap X x) = cycleComponentSupport X x := by
  apply Set.Subset.antisymm (range_cycleComponentMap_subset X x)
  intro z hz
  exact ⟨cycleComponentComplexPointLift X x z hz,
    cycleComponentMap_lift X x z hz⟩

/-- The smooth locus of a cycle component is analytically open in that component. -/
lemma isOpen_cycleComponentSmoothAnalyticLocus
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    @IsOpen
      (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
      Point.analyticTopology
      (cycleComponentSmoothAnalyticLocus X x) :=
  Point.isOpen_overOpen _

/-- The analytic smooth locus of every reduced integral cycle component is nonempty. -/
lemma cycleComponentSmoothAnalyticLocus_nonempty
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    (cycleComponentSmoothAnalyticLocus X x).Nonempty :=
  exists_cycleComponent_smooth_complexPoint X x

/-- The smooth part of a component lies in its closed analytic support. -/
lemma cycleComponentSmoothSupport_subset
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    cycleComponentSmoothSupport X x ⊆ cycleComponentSupport X x := by
  rintro z ⟨w, -, rfl⟩
  exact range_cycleComponentMap_subset X x ⟨w, rfl⟩

/-- Every reduced integral cycle component has a smooth point in its analytic support. -/
lemma cycleComponentSmoothSupport_nonempty
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    (cycleComponentSmoothSupport X x).Nonempty := by
  obtain ⟨z, hz⟩ := cycleComponentSmoothAnalyticLocus_nonempty X x
  exact ⟨cycleComponentMap X x z, z, hz, rfl⟩

/-- Membership in the smooth part of a component support can be checked on the canonical lift
to the reduced component. -/
lemma mem_cycleComponentSmoothSupport_iff
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) :
    z ∈ cycleComponentSmoothSupport X x ↔
      ∃ hz : z ∈ cycleComponentSupport X x,
        (cycleComponentComplexPointLift X x z hz).underlying ∈
          (cycleComponentι X.left x ≫ X.hom).smoothLocus := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    let hz : cycleComponentMap X x w ∈ cycleComponentSupport X x :=
      range_cycleComponentMap_subset X x ⟨w, rfl⟩
    refine ⟨hz, ?_⟩
    have heq : cycleComponentComplexPointLift X x
        (cycleComponentMap X x w) hz = w := by
      apply cycleComponentMap_injective X x
      exact cycleComponentMap_lift X x _ hz
    rw [heq]
    exact hw
  · rintro ⟨hz, hsmooth⟩
    exact ⟨cycleComponentComplexPointLift X x z hz, hsmooth,
      cycleComponentMap_lift X x z hz⟩

/-- The support of the pushforward of a principal divisor lies in the image of its carrier. -/
lemma PrincipalDivisor.pushforwardCycle_support_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    D.pushforwardCycle.support ⊆ Set.range D.inclusion := by
  unfold PrincipalDivisor.pushforwardCycle AlgebraicCycle.map
  apply Function.locallyFinsupp.support_map_subset_of_forall_mem
    (s := Set.univ) (t := Set.range D.inclusion)
  · exact Set.subset_univ _
  · exact fun x _ _ => ⟨x, rfl⟩

/-- The geometric support of a pushed-forward principal divisor lies in its closed carrier. -/
lemma PrincipalDivisor.algebraicCycleSupport_pushforwardCycle_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    algebraicCycleSupport X D.pushforwardCycle ⊆ Set.range D.inclusion := by
  let := D.isClosedImmersion
  rw [algebraicCycleSupport, Set.iUnion₂_subset_iff]
  intro x hx
  refine closure_minimal ?_ D.inclusion.isClosedEmbedding.isClosed_range
  simpa only [Set.singleton_subset_iff] using D.pushforwardCycle_support_subset_range hx

/-- The analytic support of a principal-divisor carrier is closed. -/
lemma isClosed_principalDivisorCarrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) :
    IsClosed (principalDivisorCarrierSupport X D) := by
  let := D.isClosedImmersion
  let Z : TopologicalSpace.Closeds X.left :=
    ⟨Set.range D.inclusion, D.inclusion.isClosedEmbedding.isClosed_range⟩
  exact isClosed_complexPoint_underlying_preimage X Z

/-- The analytic support of a pushed-forward principal divisor lies over its carrier. -/
lemma analyticCycleSupport_pushforwardCycle_subset_carrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) :
    analyticCycleSupport X D.pushforwardCycle ⊆
      principalDivisorCarrierSupport X D :=
  fun _ hz => D.algebraicCycleSupport_pushforwardCycle_subset_range hz

/-- The analytic support of a cycle is the union of the analytic supports of its nonzero
components. -/
lemma analyticCycleSupport_eq_iUnion {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    analyticCycleSupport X c =
      ⋃ x ∈ c.support, cycleComponentSupport X x := by
  ext z
  simp [analyticCycleSupport, algebraicCycleSupport, cycleComponentSupport]

/-- The analytic support of an algebraic cycle on a projective variety is closed. -/
lemma isClosed_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    IsClosed (analyticCycleSupport X c) := by
  rw [analyticCycleSupport_eq_iUnion]
  exact (algebraicCycle_support_finite X c).isClosed_biUnion fun x _ =>
    isClosed_cycleComponentSupport X x

lemma cycleComponentSupport_subset_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R)
    (x : X.left) (hx : c x ≠ 0) :
    cycleComponentSupport X x ⊆ analyticCycleSupport X c :=
  fun _ hz => Set.mem_iUnion₂.mpr ⟨x, Function.mem_support.mpr hx, hz⟩

@[simp]
lemma algebraicCycleSupport_zero {R : Type*} [Zero R] (X : Scheme) :
    algebraicCycleSupport X (0 : AlgebraicCycle X R) = ∅ := by
  simp [algebraicCycleSupport]
  exact fun _ => rfl

@[simp]
lemma analyticCycleSupport_zero {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    analyticCycleSupport X (0 : AlgebraicCycle X.left R) = ∅ := by
  simp [analyticCycleSupport]

end AlgebraicGeometry
