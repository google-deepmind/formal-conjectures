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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.CohomologySheafSection
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueCohomologyLowerVanishing
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueCokernelPreservation

/-!
# Lowest-degree cohomology comparison for flasque complexes

For a bounded-below termwise-flasque sheaf complex with cohomology sheaves zero below `n`,
the canonical map from cohomology of sections on any open `U` to sections of its degree-`n`
cohomology sheaf is an isomorphism, exhibited as the sheafification unit/counit comparison.
The proof shows the degree-`n` cohomology presheaf is already a sheaf, deriving flasqueness
of the preceding cycles from the lower vanishing and cokernel preservation from that.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The kernel of the actual boundary-to-cycles map is the preceding cycle sheaf. -/
def kernelBoundaryToCyclesIso (n : ℤ) :
    kernel (K.sc n).toCycles ≅ K.cycles ((ComplexShape.up ℤ).prev n) := by
  let p := (ComplexShape.up ℤ).prev n
  have hp : p = n - 1 := (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk _ _ (by omega))
  have hnext : (ComplexShape.up ℤ).next p = n :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk _ _ (by rw [hp]; omega))
  exact (kernelCompMono (K.sc n).toCycles (K.sc n).iCycles).symm ≪≫
    kernelIsoOfEq (K.sc n).toCycles_i ≪≫
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (K.sc n).f) (K.cyclesIsKernel p n hnext)

/-- In the first potentially nonzero cohomology degree, the forgetful functor
preserves the actual left homology of this short complex. -/
private theorem forget_preservesLeftHomologyOf_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (forget AddCommGrpCat.{u} X).PreservesLeftHomologyOf (K.sc n) := by
  let F := forget AddCommGrpCat.{u} X
  let p := (ComplexShape.up ℤ).prev n
  have hp : p = n - 1 := (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk _ _ (by omega))
  let : (K.cycles p).IsFlasque :=
    IsFlasque.BoundedBelowComplex.cycles_isFlasque_of_exact_le K N (n - 1)
      (fun j hj => (K.exactAt_iff_isZero_homology j).mpr (hK j (by omega)))
      hflasque p (by rw [hp])
  let : (F.obj (K.cycles ((ComplexShape.up ℤ).prev n))).IsFlasque :=
    inferInstanceAs ((K.cycles p).IsFlasque)
  let : (kernel (K.sc n).toCycles).IsFlasque :=
    TopCat.Presheaf.IsFlasque.of_iso (F.mapIso (kernelBoundaryToCyclesIso X K n))
  let : (K.sc n).X₁.IsFlasque := hflasque p
  let : (ShortComplex.LeftHomologyData.canonical (K.sc n)).IsPreservedBy F :=
    { g := inferInstance
      f' := IsFlasque.forget_preservesCokernel (K.sc n).toCycles }
  exact Functor.PreservesLeftHomologyOf.mk' F (ShortComplex.LeftHomologyData.canonical (K.sc n))

/-- The lowest-degree section-cohomology presheaf is an actual sheaf. -/
private theorem sectionCohomologyPresheaf_isSheaf_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (sectionCohomologyPresheaf X K n) := by
  let := forget_preservesLeftHomologyOf_lowest X K N n hK hflasque
  let e : sectionCohomologyPresheaf X K n ≅ (K.homology n).obj :=
    (K.sc n).mapHomologyIso (forget AddCommGrpCat.{u} X)
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mpr (K.homology n).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual presheaf-to-cohomology-sheaf comparison is an isomorphism, because
its literal sheafification unit is an isomorphism in this degree. -/
private theorem sectionCohomologyPresheafToSheaf_isIso_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    IsIso (sectionCohomologyPresheafToSheaf X K n) := by
  let := isIso_toSheafify (Opens.grothendieckTopology X)
    (sectionCohomologyPresheaf_isSheaf_lowest X K N n hK hflasque)
  dsimp only [sectionCohomologyPresheafToSheaf]
  infer_instance

/-- Lowest-degree cohomology of sections equals sections of the cohomology sheaf
on every open, via the already defined canonical comparison map. -/
theorem sectionCohomologyToSheafSection_isIso_lowest (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) : IsIso (sectionCohomologyToSheafSection X K n U) := by
  let := sectionCohomologyPresheafToSheaf_isIso_lowest X K N n hK hflasque
  dsimp only [sectionCohomologyToSheafSection]
  infer_instance

/-- The constructed lowest-degree isomorphism, with the actual comparison as its
forward map. Taking `U = ⊤` gives the global-sections isomorphism. -/
def lowestSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅
      (K.homology n).obj.obj (op U) := by
  let := sectionCohomologyToSheafSection_isIso_lowest X K N n hK hflasque U
  exact asIso (sectionCohomologyToSheafSection X K n U)

/-- In particular, the actual lowest-degree global section-complex cohomology
is canonically isomorphic to global sections of the cohomology sheaf. -/
def lowestGlobalSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (IsFlasque.BoundedBelowComplex.globalSectionsComplex K).homology n ≅
      (K.homology n).obj.obj (op (⊤ : Opens X)) :=
  lowestSectionCohomologyIso X K N n hK hflasque ⊤

end TopCat.Sheaf
