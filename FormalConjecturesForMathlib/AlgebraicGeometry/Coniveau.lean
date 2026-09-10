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

public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleClass

/-!
# The coniveau subspace

For a projective complex variety, a class supported on a closed set `Z` belongs to the homotopy
fiber of `RΓ(X, ℚ) → RΓ(X ∖ Z, ℚ)`, and its image in ordinary cohomology is the canonical
connecting map. The sum of these images over codimension-`p` algebraic subsets is the coniveau
subspace.

It is only an upper bound for the span of cycle classes until cohomological purity has been
proved: an arbitrary supported cohomology class is not, by definition, a fundamental class. The
construction is therefore kept explicitly named as such, alongside an intrinsic component line
defined from generators of the entire supported image, for stating comparison theorems. The
algebraic cycle-class span itself is defined from the actual normalized component classes of
`CycleComponentSheafClass`, and the two agree once purity holds.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- Rational constant-sheaf cohomology supported on a closed subset of an analytification. -/
abbrev RationalConstantSheafCohomologyWithSupport
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :=
  RationalCohomologyWithSupport X Z n

/-- The rational span in ordinary cohomology of classes supported on `Z`. -/
def rationalCohomologySupportedOn
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :
    Submodule ℚ (FieldCohomology ℚ X n) :=
  Submodule.span ℚ (Set.range (forgetSupport X Z n))

/-- A class which generates the whole degree-`2p` image of cohomology supported on one
irreducible component. This is a property inside ordinary rational cohomology; it does not assume
that the supported image is one-dimensional. Cohomological purity proves that such a generator
is precisely a nonzero rational multiple of the component's fundamental class. -/
def IsRationalComponentCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (x : X.left) (α : FieldCohomology ℚ X (2 * (p : ℤ))) : Prop :=
  α ∈ rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ)) ∧
    Submodule.span ℚ {α} =
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ))

/-- The intrinsic cycle-class line of an irreducible codimension-`p` component. Taking the span
of all generators removes the arbitrary choice of generator and its rational scaling. -/
def rationalComponentCycleClassLine
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  Submodule.span ℚ {α | IsRationalComponentCycleClass X p x α}

/-- Any generator of the supported image computes the same intrinsic component line. -/
lemma rationalComponentCycleClassLine_eq_span
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) (x : X.left)
    (α : FieldCohomology ℚ X (2 * (p : ℤ)))
    (hα : IsRationalComponentCycleClass X p x α) :
    rationalComponentCycleClassLine X p x = Submodule.span ℚ {α} :=
  le_antisymm (Submodule.span_le.mpr fun _ hβ ↦ hα.2.ge hβ.1)
    (Submodule.span_mono (Set.singleton_subset_iff.mpr hα))

/-- Cohomological purity for a component, stated independently of the construction of any
particular supported class: its fundamental-class line is the whole supported image in the
critical degree. -/
def RationalComponentCycleClassPurity
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) : Prop :=
  rationalComponentCycleClassLine X p x =
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

lemma rationalComponentCycleClassLine_eq_supportedOn_of_purity
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) (x : X.left)
    (h : RationalComponentCycleClassPurity X p x) :
    rationalComponentCycleClassLine X p x =
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  h

/-- The component cycle-class line lies in the image of cohomology supported on that component. -/
lemma rationalComponentCycleClassLine_le_supportedOn
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) :
    rationalComponentCycleClassLine X p x ≤
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  Submodule.span_le.mpr fun _ hα ↦ hα.1

/-- The rational span of the actually constructed codimension-`p` component classes.

The relative dimension is the canonical `dim X`, whose certificate is proved from smoothness and
integrality. This definition spans explicit class terms; it does not quantify over hypothetical
generators and does not assume descent to the Chow group. -/
def algebraicCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx}

@[simp]
lemma algebraicCycleClassSpan_zero
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 0 =
      ⨆ (x : X.left) (hx : coheight x = 0),
        Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} :=
  rfl

lemma algebraicCycleClassSpan_of_ne_zero
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (_hp : p ≠ 0) :
    algebraicCycleClassSpan X p =
      ⨆ (x : X.left) (hx : coheight x = p),
        Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} :=
  rfl

/-- Every ordinary rational cohomology class is represented with support on the whole analytic
space. -/
lemma rationalCohomologySupportedOn_univ_eq_top
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℤ) :
    rationalCohomologySupportedOn X Set.univ n = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨β, hβ⟩ := forgetSupport_surjective_univ X n α
  exact Submodule.subset_span ⟨β, hβ⟩

/-- The component belonging to the generic point of an integral variety has the whole analytic
space as its support. -/
lemma cycleComponentSupport_genericPoint_eq_univ
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSupport X (genericPoint X.left) = Set.univ := by
  rw [cycleComponentSupport]
  change (@Point.underlying ℂ _ _ X) ⁻¹'
    (closure {genericPoint X.left} : Set X.left) = Set.univ
  rw [genericPoint_closure (α := X.left)]
  exact Set.preimage_univ

/-- The degree-`2p` rational coniveau subspace obtained from all cohomology classes supported on
irreducible algebraic subvarieties of codimension `p`. This is not the cycle-class span unless a
purity theorem identifying each relevant image with its fundamental-class line is supplied. -/
def rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  ⨆ (x : X.left) (_ : coheight x = p),
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

/-- In codimension zero, the degree-zero coniveau subspace is all rational cohomology because
support on the whole space imposes no condition. This is a statement about coniveau, not about
the span of the codimension-zero cycle class. -/
lemma rationalConiveauSubspace_zero_eq_top
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalConiveauSubspace X 0 = ⊤ := by
  apply top_unique
  rw [← rationalCohomologySupportedOn_univ_eq_top X 0,
    ← cycleComponentSupport_genericPoint_eq_univ X]
  apply le_iSup_of_le (genericPoint X.left)
  apply le_iSup_of_le (Order.IsMax.coheight_eq_zero isMax_top)
  rfl

/-- Forgetting the support of a class on one codimension-`p` component lands in the corresponding
coniveau subspace. -/
lemma forgetSupport_mem_rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (x : X.left) (hx : coheight x = p)
    (α : RationalConstantSheafCohomologyWithSupport X
      (cycleComponentSupport X x) (2 * (p : ℤ))) :
    forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) α ∈
      rationalConiveauSubspace X p := by
  apply (le_iSup (fun x : X.left => ⨆ hx : coheight x = p,
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) x)
  apply (le_iSup (fun _ : coheight x = p =>
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) hx)
  exact Submodule.subset_span ⟨α, rfl⟩

/-- Every constructed algebraic cycle class has coniveau at least its codimension. -/
lemma algebraicCycleClassSpan_le_rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    algebraicCycleClassSpan X p ≤ rationalConiveauSubspace X p := by
  refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  apply Submodule.span_le.mpr
  intro α hα
  rw [Set.mem_singleton_iff] at hα
  subst α
  apply (le_iSup (fun x : X.left => ⨆ hx : coheight x = p,
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) x)
  apply (le_iSup (fun _ : coheight x = p =>
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) hx)
  rw [cycleComponentSheafClass_eq_forgetSupport]
  exact Submodule.subset_span ⟨cycleComponentSheafSupportedClass
    X x (d := dim X.left) hx, rfl⟩

/-- If every constructed component class spans its entire supported image, the algebraic
cycle-class span agrees with the coniveau subspace. The equality for each component is an
explicit hypothesis; it is not built into either construction. -/
lemma algebraicCycleClassSpan_eq_rationalConiveauSubspace_of_purity
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (h : ∀ (x : X.left) (hx : coheight x = p),
      Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} =
        rationalCohomologySupportedOn X
          (cycleComponentSupport X x) (2 * (p : ℤ))) :
    algebraicCycleClassSpan X p = rationalConiveauSubspace X p := by
  refine le_antisymm (algebraicCycleClassSpan_le_rationalConiveauSubspace X p)
    (iSup_le fun x ↦ iSup_le fun hx ↦ ?_)
  rw [← h x hx]
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

end AlgebraicGeometry.ComplexPoint
