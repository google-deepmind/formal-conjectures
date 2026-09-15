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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ReducedSmoothClosedFiltrationDimension
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothStratificationAnalytification
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothAffineRelativeDimension
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexOpen

/-!
# Ambient closed supports for singular-component localization induction

The singular boundary of an integral cycle component carries its canonical finite reduced
smooth filtration, whose images are closed both algebraically and analytically in the ambient
variety, and whose successive differences are the complex-point images of smooth locally
closed strata. Their local relative dimensions are strictly below `d - p`, so their ambient
normal codimensions are at least `p + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

/-- The canonical closed remainders inside the integral component's singular boundary. -/
abbrev cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (cycleComponent X.left x) :=
  reducedSmoothClosedFiltration (cycleComponentι X.left x ≫ X.hom)
    (singularLocusClosed (cycleComponentι X.left x ≫ X.hom)) k

/-- The exact terminal index is read from the already constructed finite decomposition. -/
abbrev cycleComponentSingularFiltrationLength : ℕ :=
  (cycleComponentSingularStratification X x).length

/-- The actual smooth scheme occurring between two consecutive closed supports. -/
abbrev cycleComponentSingularFiltrationStratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece (cycleComponentι X.left x ≫ X.hom)
    (cycleComponentSingularClosedFiltration X x k)

/-- Its actual locally closed immersion into the original smooth ambient scheme. -/
def cycleComponentSingularFiltrationStratumι (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶ X.left :=
  reducedClosedSmoothPieceι (cycleComponentι X.left x ≫ X.hom)
    (cycleComponentSingularClosedFiltration X x k) ≫ cycleComponentι X.left x

/-- A singular-filtration stratum with its induced structure map to `Spec ℂ`. -/
abbrev cycleComponentSingularFiltrationStratumOver (k : ℕ) : Over (Spec (.of ℂ)) :=
  Over.mk (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)

/-- The stratum immersion bundled over `Spec ℂ`. -/
def cycleComponentSingularFiltrationStratumOverι (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶ X :=
  Over.homMk (cycleComponentSingularFiltrationStratumι X x k) rfl

instance cycleComponentSingularFiltrationStratumOverι_isImmersion (k : ℕ) :
    IsImmersion (cycleComponentSingularFiltrationStratumOverι X x k).left := by
  change IsImmersion (reducedClosedSmoothPieceι (cycleComponentι X.left x ≫ X.hom)
    (cycleComponentSingularClosedFiltration X x k) ≫ cycleComponentι X.left x)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance cycleComponentSingularFiltrationStratumι_isImmersion (k : ℕ) :
    IsImmersion (cycleComponentSingularFiltrationStratumι X x k) := by
  dsimp [cycleComponentSingularFiltrationStratumι]
  infer_instance

instance cycleComponentSingularFiltrationStratum_smooth (k : ℕ) :
    Smooth (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  change Smooth ((reducedClosedSmoothPieceι (cycleComponentι X.left x ≫ X.hom)
    (cycleComponentSingularClosedFiltration X x k) ≫ cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

instance cycleComponentSingularFiltrationStratumOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (cycleComponentSingularFiltrationStratumOver X x k).hom := by
  change LocallyOfFiniteType (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
  infer_instance

/-- Every stage is a closed support in the original algebraic ambient scheme. -/
def cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨cycleComponentι X.left x '' (cycleComponentSingularClosedFiltration X x k : Set _),
    (cycleComponentι X.left x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularClosedFiltration X x k).isClosed⟩

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The successive ambient difference is precisely the image of the actual smooth stratum. -/
theorem cycleComponentSingularAmbientClosedFiltration_layer (k : ℕ) :
    Set.range (cycleComponentSingularFiltrationStratumι X x k) =
      (cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) \
        (cycleComponentSingularAmbientClosedFiltration X x (k + 1) : Set X.left) := by
  rw [cycleComponentSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (cycleComponentι X.left x).isClosedEmbedding.injective _ _

/-- The exact ambient open used by the consecutive-support localization triangle. -/
def cycleComponentSingularStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (cycleComponentSingularAmbientClosedFiltration X x (k + 1)).compl

/-- The actual smooth stratum factors into the complement of the next closed support. -/
def cycleComponentSingularStratumClosedLift (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶
      cycleComponentSingularStratumAmbientOpen X x k :=
  IsOpenImmersion.lift (cycleComponentSingularStratumAmbientOpen X x k).ι
    (cycleComponentSingularFiltrationStratumι X x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((cycleComponentSingularAmbientClosedFiltration_layer X x k).le hy).2)

/-- The localization open with its induced structure map to `Spec ℂ`. -/
abbrev cycleComponentSingularStratumAmbientOpenOver (k : ℕ) : Over (Spec (.of ℂ)) :=
  ComplexPoint.openScheme X (cycleComponentSingularStratumAmbientOpen X x k)

instance cycleComponentSingularStratumAmbientOpenOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (cycleComponentSingularStratumAmbientOpenOver X x k).hom := by
  change LocallyOfFiniteType
    ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem cycleComponentSingularStratumClosedLift_ι (k : ℕ) :
    cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι =
        cycleComponentSingularFiltrationStratumι X x k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift bundled over `Spec ℂ`. -/
def cycleComponentSingularStratumClosedLiftOver (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶
      cycleComponentSingularStratumAmbientOpenOver X x k :=
  Over.homMk (cycleComponentSingularStratumClosedLift X x k) (by
    change cycleComponentSingularStratumClosedLift X x k ≫
      ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) =
        cycleComponentSingularFiltrationStratumι X x k ≫ X.hom
    rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι])

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Its closed image is exactly the restriction of the current support to that open. -/
theorem range_cycleComponentSingularStratumClosedLift (k : ℕ) :
    Set.range (cycleComponentSingularStratumClosedLift X x k) =
      (cycleComponentSingularStratumAmbientOpen X x k).ι ⁻¹'
        (cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) := by
  have hf (w : cycleComponentSingularFiltrationStratum X x k) :
      (cycleComponentSingularStratumAmbientOpen X x k).ι
        (cycleComponentSingularStratumClosedLift X x k w) =
          cycleComponentSingularFiltrationStratumι X x k w :=
    congrArg (fun f => f w) (cycleComponentSingularStratumClosedLift_ι X x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((cycleComponentSingularAmbientClosedFiltration_layer X x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (cycleComponentSingularAmbientClosedFiltration_layer X x k).ge ⟨hy, y.2⟩
    exact ⟨w, (cycleComponentSingularStratumAmbientOpen X x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

/-- Each actual layer is a closed immersion in precisely the open needed by localization,
not in an unrelated auxiliary open. -/
instance cycleComponentSingularStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k) := by
  have : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι) := by
    rw [cycleComponentSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k) :=
    .of_comp (cycleComponentSingularStratumClosedLift X x k)
      (cycleComponentSingularStratumAmbientOpen X x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_cycleComponentSingularStratumClosedLift]
  exact (cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
    (cycleComponentSingularStratumAmbientOpen X x k).ι.continuous

instance cycleComponentSingularStratumClosedLiftOver_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLiftOver X x k).left := by
  change IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k)
  infer_instance

/-- The actual localization open remains smooth of the original ambient dimension. -/
instance cycleComponentSingularStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    SmoothOfRelativeDimension d ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSingularStratumAmbientOpen X x k).ι X.hom

instance cycleComponentSingularStratumClosedLift_smooth (k : ℕ) :
    Smooth (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι]
  infer_instance

namespace ComplexPoint

local instance cycleComponentSingularClosedFiltrationAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The actual analytically closed ambient supports for nested-support localization. -/
def cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (cycleComponentSingularAmbientClosedFiltration X x k : Set X.left),
    (cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
      (continuous_underlying_to_zariski X)⟩

/-- The smooth locus of the component, bundled over `Spec ℂ`. -/
abbrev cycleComponentSmoothLocusOver : Over (Spec (.of ℂ)) :=
  Over.mk (((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    cycleComponentι X.left x) ≫ X.hom)

/-- The smooth-locus immersion into the ambient variety, bundled over `Spec ℂ`. -/
def cycleComponentSmoothLocusOverι : cycleComponentSmoothLocusOver X x ⟶ X :=
  Over.homMk ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    cycleComponentι X.left x) rfl

instance cycleComponentSmoothLocusOverι_isImmersion :
    IsImmersion (cycleComponentSmoothLocusOverι X x).left := by
  change IsImmersion ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    cycleComponentι X.left x)
  infer_instance

instance cycleComponentSmoothLocusOver_locallyOfFiniteType :
    LocallyOfFiniteType (cycleComponentSmoothLocusOver X x).hom := by
  change LocallyOfFiniteType
    (((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

end ComplexPoint
end AlgebraicGeometry
