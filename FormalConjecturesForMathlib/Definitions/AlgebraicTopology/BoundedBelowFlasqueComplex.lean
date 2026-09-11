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

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Global sections of bounded-below exact flasque complexes

An exact bounded-below cochain complex of flasque sheaves remains exact after taking global
sections.  The proof is elementary: starting at the lower bound, the cycle sheaves are flasque
by induction through their short exact sequences.  Global sections are then exact on each of
those sequences.

This is the acyclic-complex lemma needed to compare a bounded-below flasque resolution with a
termwise-injective replacement.  It does not assume or invoke a hypercohomology spectral
sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf.IsFlasque

universe u

variable {X : TopCat.{u}}

namespace BoundedBelowComplex

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The short exact sequence from cycles in degree `i`, through the degree-`i` term, to cycles
in degree `i + 1`. -/
def cyclesShortComplex (i : ℤ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1))]
    simp)

/-- Evaluation of a sheaf on the top open subset, viewed as a functor. -/
def globalSectionsFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

noncomputable instance globalSectionsFunctor_additive :
    (globalSectionsFunctor X).Additive := by
  constructor
  intro A B f g
  change (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))).map
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (f + g))) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

noncomputable instance globalSectionsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (globalSectionsFunctor X) := by
  let : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))) :=
    inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))

/-- The integer-indexed cochain complex obtained by evaluating a sheaf complex on the top open
subset. -/
def globalSectionsComplex
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

end BoundedBelowComplex

end TopCat.Sheaf.IsFlasque
