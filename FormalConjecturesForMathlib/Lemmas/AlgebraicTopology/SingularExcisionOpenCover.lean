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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCoverSmallQuasiIso

import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionRelativeMesh
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionSupport

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Small-chain approximation for open covers

This file assembles the geometric affine-mesh theorem, the exact permutation-ancestry expansion,
the adaptive quasi-isomorphism argument, and projectivity.  The result is the classical
small-singular-chain theorem for every open cover, with no additional hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology.Singular

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The cover-small inclusion is a quasi-isomorphism for every open cover. -/
public theorem coverSmallChainQuasiIsomorphism_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coverSmallIntegralSingularChainInclusion X U) :=
  coverSmallChainQuasiIsomorphism_of_eventuallySmall X U
    (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

/-- Classical small-chain approximation: the inclusion of chains subordinate to an open cover is
a chain-homotopy equivalence for integral singular chains. -/
public theorem coverSmallChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (coverSmallIntegralSingularChainInclusion X U) :=
  coverSmallChainApproximation_of_eventuallySmall X U
    (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

/-- A selected chain-homotopy equivalence witnessing small-chain approximation. -/
public noncomputable def coverSmallChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallIntegralSingularChainComplex X U)
      (IntegralSingularChainComplexObj X) :=
  (coverSmallChainApproximation_of_openCover X U hUopen hUcover).choose

public theorem coverSmallChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom =
      coverSmallIntegralSingularChainInclusion X U :=
  (coverSmallChainApproximation_of_openCover X U hUopen hUcover).choose_spec

/-- Small-chain approximation gives the expected homology isomorphism in every degree. -/
public noncomputable def coverSmallIntegralSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).homology n ≅
      (IntegralSingularChainComplexObj X).homology n :=
  (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).toHomologyIso n

public theorem coverSmallIntegralSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallIntegralSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallIntegralSingularChainInclusion X U) n := by
  change HomologicalComplex.homologyMap
    (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom n = _
  rw [coverSmallChainHomotopyEquiv_of_openCover_hom]


end AlgebraicTopology.Singular
