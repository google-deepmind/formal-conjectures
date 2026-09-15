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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.Points

import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation
import FormalConjecturesForMathlib.Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Points over a commutative ring, and analytification

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.Points`.
-/

@[expose] public section

open CategoryTheory Topology
open scoped CommRingCat.HomTopology

namespace AlgebraicGeometry

variable (R : Type) [CommRing R]

namespace Point

variable {R}

section Functoriality

variable {X Y Z : Over (Spec ↧R)}

end Functoriality

section IsLocalRing

variable [IsLocalRing R] {X : Over (Spec ↧R)}

lemma evaluate_eq_evaluateOnOpen (U : X.left.Opens) (s : Γ(X.left, U))
    (z : OverOpen (X := X) U) :
    evaluate U s z.1 = evaluateOnOpen U s z := by
  rw [evaluate, dif_pos z.2]
  rfl

section Topology

variable [TopologicalSpace R]

variable [ContinuousMul R] [IsOpenUnits R]

/-- The `R`-points over a scheme open form an analytic open set. -/
lemma isOpen_overOpen (U : X.left.Opens) :
    IsOpen (overOpen U : Set (Point R X)) := by
  simpa using isOpen_overOpen_inter_preimage U 0 Set.univ isOpen_univ

end Topology

end IsLocalRing

section Field

variable {K : Type} [Field K] {X : Over (Spec ↧K)}

lemma residueData_fst (z : Point K X) : z.residueData.1 = z.underlying := rfl

lemma residue_comp_residueData_snd (z : Point K X) :
    X.left.residue z.underlying ≫ z.residueData.2 = z.stalkHom :=
  Scheme.residue_descResidueField (X := X.left) z.stalkHom

/-- Over a field, evaluation is evaluation in the residue field. -/
lemma evaluate_eq_residueData (U : X.left.Opens) (s : Γ(X.left, U)) (z : Point K X)
    (hz : z ∈ overOpen U) :
    evaluate U s z = z.residueData.2 (X.left.evaluation U z.underlying hz s) := by
  rw [evaluate, dif_pos (show z.underlying ∈ U from hz), ← residue_comp_residueData_snd z]
  rfl

/-- Over a field, a `K`-point belongs to a principal open exactly when its defining function is
nonzero there. -/
lemma mem_overOpen_basicOpen_iff_evaluate_ne_zero {U : X.left.Opens} (s : Γ(X.left, U))
    (z : Point K X) (hz : z ∈ overOpen U) :
    z ∈ overOpen (X.left.basicOpen s) ↔ evaluate U s z ≠ 0 := by
  rw [mem_overOpen_basicOpen_iff_isUnit_evaluate s z hz, isUnit_iff_ne_zero]

/-- Over a field, a regular function on a principal open of an affine open is a genuine quotient
of regular functions on the whole affine open. -/
lemma exists_evaluate_basicOpen_eq_div {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (t : Γ(X.left, X.left.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X.left, U)), ∀ z : Point K X,
      z ∈ overOpen (X.left.basicOpen f) →
        evaluate (X.left.basicOpen f) t z = evaluate U a z / evaluate U f z ^ k := by
  obtain ⟨k, a, h⟩ :=
    exists_evaluate_basicOpen_eq_inverse_mul (X := X) hU f t
  exact ⟨k, a, fun z hz ↦ by rw [h z hz, Ring.inverse_eq_inv', div_eq_inv_mul]⟩

/-- The residue-field description of the image of a `K`-point. Both the underlying point and
its residue-field embedding are obtained functorially. -/
lemma residueData_map {Y : Over (Spec ↧K)} (f : X ⟶ Y) (z : Point K X) :
    (map f z).residueData =
      ⟨f.left z.residueData.1, f.left.residueFieldMap z.residueData.1 ≫ z.residueData.2⟩ := by
  apply Sigma.ext
  · simp [map, residueData, Scheme.SpecToEquivOfField]
    rfl
  · dsimp [map, residueData, Scheme.SpecToEquivOfField]
    rw [Scheme.descResidueField_stalkClosedPointTo_comp]

lemma residueData_map_snd {Y : Over (Spec ↧K)} (f : X ⟶ Y) (z : Point K X) :
    (map f z).residueData.2 =
      f.left.residueFieldMap z.residueData.1 ≫ z.residueData.2 := by
  dsimp [map, residueData, Scheme.SpecToEquivOfField]
  rw [Scheme.descResidueField_stalkClosedPointTo_comp]

end Field

end Point

end AlgebraicGeometry
