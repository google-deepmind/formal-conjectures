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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ReducedSmoothClosedFiltration
public import FormalConjecturesForMathlib.AlgebraicGeometry.SingularLocusDimension
public import FormalConjecturesForMathlib.AlgebraicTopology.NowhereDenseDimensionDrop

/-!
# Dimension drop at every actual reduced singular-filtration step

Unlike the integral first-step bound, subsequent closed remainders may be reducible.
The dense smooth locus and the Noetherian nowhere-dense dimension theorem prove the
same strict finite upper-bound drop on every remainder. These are algebraic dimension
results, not assumed analytic cohomological bounds.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [NoetherianSpace X]

/-- The singular complement of a reduced Noetherian scheme loses a finite dimension
bound even when the scheme is reducible. -/
theorem topologicalKrullDim_reducedSingularLocus_lt_of_isReduced [IsReduced X]
    {n : ℕ} (hdim : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (reducedSingularLocus f) < n := by
  apply topologicalKrullDim_lt_of_isClosed_of_dense_compl
    (singularLocusClosed f).isClosed _ hdim
  simpa only [singularLocusClosed, Opens.coe_compl, compl_compl] using
    f.dense_smoothLocus_of_perfectField

omit [PerfectField K] [NoetherianSpace X] in
/-- Transporting the actual singular complement into the original ambient closed set
preserves its topology and therefore its dimension. -/
theorem topologicalKrullDim_reducedClosedSingularRemainder_eq (S : Closeds X) :
    topologicalKrullDim (reducedClosedSingularRemainder f S) =
      topologicalKrullDim (reducedSingularLocus (reducedClosedStructureMap f S)) := by
  let e := (reducedClosedSubschemeι S).isClosedEmbedding.isEmbedding.homeomorphImage
    (((reducedClosedStructureMap f S).smoothLocus : Set (reducedClosedSubscheme S))ᶜ)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- Every canonical remainder strictly lowers any finite dimension bound for its
preceding closed support. No irreducibility hypothesis is imposed on that support. -/
theorem topologicalKrullDim_reducedClosedSingularRemainder_lt (S : Closeds X)
    {n : ℕ} (hdim : topologicalKrullDim S ≤ n) :
    topologicalKrullDim (reducedClosedSingularRemainder f S) < n := by
  rw [topologicalKrullDim_reducedClosedSingularRemainder_eq]
  let : NoetherianSpace (reducedClosedSubscheme S) :=
    (reducedClosedSubschemeι S).isClosedEmbedding.isInducing.noetherianSpace
  exact topologicalKrullDim_reducedSingularLocus_lt_of_isReduced
    (reducedClosedStructureMap f S) hdim

/-- The strict dimension drop is available directly at every successive filtration pair. -/
theorem topologicalKrullDim_reducedSmoothClosedFiltration_succ_lt (S : Closeds X)
    (k : ℕ) {n : ℕ} (hdim : topologicalKrullDim (reducedSmoothClosedFiltration f S k) ≤ n) :
    topologicalKrullDim (reducedSmoothClosedFiltration f S (k + 1)) < n :=
  topologicalKrullDim_reducedClosedSingularRemainder_lt f _ hdim

end AlgebraicGeometry
