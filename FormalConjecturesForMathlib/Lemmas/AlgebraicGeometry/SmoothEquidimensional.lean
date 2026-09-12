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

public import FormalConjecturesForMathlib.Lemmas.Topology.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentDimension
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Smooth integral complex schemes are equidimensional

A smooth morphism to `Spec ℂ` is standard smooth of *some* relative dimension near each point, but
the class `SmoothOfRelativeDimension` demands one dimension that works everywhere. This file shows
that on an integral scheme there is such a dimension, and that it is `dim X`.

The argument is that the relative dimension of an affine chart is the Krull dimension of its
sections, and that any two nonempty opens of an irreducible space meet: shrinking a chart to a
basic open inside another chart compares the two dimensions, and doing this in both directions
makes them equal. Once a single relative dimension is known to work, the existing global formula
`SmoothOfRelativeDimension.orderKrullDim_eq_complex` identifies it with `dim X`.

The resulting instance is what lets constructions on a smooth integral complex scheme drop their
relative-dimension parameter and recover it from the scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Spec ↧ℂ)

/-- A standard-smooth ring map is standard smooth of some relative dimension, read off from any
submersive presentation. -/
lemma RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension {R S : Type*}
    [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  let := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

/-- Shrinking an affine chart to a basic open preserves the relative dimension, because sections
over the basic open are a localization away of the sections over the chart. -/
lemma isStandardSmoothOfRelativeDimension_appLE_basicOpen {U : X.Opens} {n : ℕ}
    (hU : IsAffineOpen U) (g : Γ(X, U))
    (h : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n) :
    (f.appLE ⊤ (X.basicOpen g) (by simp)).hom.IsStandardSmoothOfRelativeDimension n := by
  have hloc := hU.isLocalization_basicOpen g
  have key :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
      Γ(X, X.basicOpen g) g (f.appLE ⊤ U (by simp)).hom h
  have hcomp : (f.appLE ⊤ (X.basicOpen g) (by simp)).hom =
      (algebraMap Γ(X, U) Γ(X, X.basicOpen g)).comp (f.appLE ⊤ U (by simp)).hom := by
    have := f.appLE_map (U := ⊤) (V := U) (V' := X.basicOpen g) (by simp)
      (homOfLE (X.basicOpen_le g)).op
    rw [← this]
    rfl
  rwa [hcomp]

/-- On a nonempty affine chart where the structure map is standard smooth of relative dimension
`n`, the Krull dimension of the chart is `n`. -/
lemma orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension {U : X.Opens} {n : ℕ}
    (hU : IsAffineOpen U) [Nonempty U]
    (h : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n) :
    Order.krullDim U = n := by
  rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU]
  exact (algebraMap_isStandardSmoothOfRelativeDimension (Over.mk f) h).ringKrullDim_eq_complex

/-- The Krull dimension of an open subscheme does not exceed that of the ambient scheme. -/
lemma orderKrullDim_mono {U V : X.Opens} (h : U ≤ V) : Order.krullDim U ≤ Order.krullDim V := by
  rw [← Scheme.topologicalKrullDim_eq_orderKrullDim U.toScheme,
    ← Scheme.topologicalKrullDim_eq_orderKrullDim V.toScheme]
  exact (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- Half of the chart-independence, given a point in both charts: shrink the first chart to a basic
open contained in the second. -/
private lemma isStandardSmoothOfRelativeDimension_le {U V : X.Opens} {n m : ℕ}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty V]
    (hn : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n)
    (hm : (f.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension m)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n ≤ m := by
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hxU
  have hne : Nonempty (X.basicOpen g) := ⟨⟨x, hxg⟩⟩
  have hZ : Order.krullDim (X.basicOpen g) = n :=
    orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension f (hU.basicOpen g)
      (isStandardSmoothOfRelativeDimension_appLE_basicOpen f hU g hn)
  have hVdim : Order.krullDim V = m :=
    orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension f hV hm
  have := orderKrullDim_mono (X := X) hgV
  rw [hZ, hVdim] at this
  exact_mod_cast this

/-- On an integral scheme, the relative dimension of a standard-smooth affine chart does not depend
on the chart. -/
lemma isStandardSmoothOfRelativeDimension_eq [IsIntegral X] {U V : X.Opens} {n m : ℕ}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty U] [Nonempty V]
    (hn : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n)
    (hm : (f.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension m) : n = m := by
  obtain ⟨x⟩ := ‹Nonempty U›
  obtain ⟨y⟩ := ‹Nonempty V›
  obtain ⟨z, hzU, hzV⟩ : ((U : Set X) ∩ (V : Set X)).Nonempty := by
    obtain ⟨z, -, hz⟩ := (IrreducibleSpace.isIrreducible_univ X).2 (U : Set X) (V : Set X) U.2 V.2
      ⟨x.1, trivial, x.2⟩ ⟨y.1, trivial, y.2⟩
    exact ⟨z, hz⟩
  exact le_antisymm (isStandardSmoothOfRelativeDimension_le f hU hV hn hm hzU hzV)
    (isStandardSmoothOfRelativeDimension_le f hV hU hm hn hzV hzU)

/-- A smooth integral complex scheme is smooth of a single relative dimension. -/
lemma Smooth.exists_smoothOfRelativeDimension [IsIntegral X] [Smooth f] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨V₀, hV₀, hx₀, hs₀⟩ := Smooth.exists_affine_isStandardSmooth f x₀
  have hne₀ : Nonempty V₀ := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨n, hn⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs₀
  refine ⟨n, ⟨fun x ↦ ?_⟩⟩
  obtain ⟨V, hV, hxV, hs⟩ := Smooth.exists_affine_isStandardSmooth f x
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨m, hm⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  refine ⟨⊤, isAffineOpen_top _, V, hV, hxV, by simp, ?_⟩
  rwa [isStandardSmoothOfRelativeDimension_eq f hV₀ hV hn hm]

/-- A smooth integral complex scheme is smooth of relative dimension `dim X`.

This is what makes the relative dimension of a smooth integral complex scheme redundant data: it
is recovered from the scheme as `dim X`. -/
instance SmoothOfRelativeDimension.of_isIntegral [IsIntegral X] [Smooth f] :
    SmoothOfRelativeDimension (dim X) f := by
  obtain ⟨n, hn⟩ := Smooth.exists_smoothOfRelativeDimension f
  have hdim : dim X = n := by
    rw [TopologicalSpace.dim_eq_krullDim,
      SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := f) (d := n)]
    simp
  rwa [hdim]

end AlgebraicGeometry
