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

public import FormalConjecturesForMathlib.RingTheory.SmoothKrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentDimension
import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothComplexCoordinates
import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Dimension bounds for smooth complex schemes

This file proves the dimension-theoretic consequences of smooth complex coordinates that do not
require a catenary dimension formula.  Its commutative-algebra input is
`FormalConjecturesForMathlib.RingTheory.SmoothKrullDimension`, which bounds the Krull dimension of a
standard-smooth complex algebra of relative dimension `d` by `d`.

For a smooth complex scheme, the affine coordinate neighborhoods therefore give the global bound
`height x + coheight x ≤ d`.  The reverse inequality, and hence equality, is the catenary
dimension formula.  It is not a consequence of the currently available Mathlib API and is not
assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry

variable {X : Scheme}

/-- The order-theoretic Krull dimension of an affine open is the ring-theoretic Krull dimension
of its ring of sections. -/
lemma orderKrullDim_affineOpen_eq_ringKrullDim (U : X.Opens) (hU : IsAffineOpen U) :
    Order.krullDim U = ringKrullDim Γ(X, U) := by
  calc
    Order.krullDim U = topologicalKrullDim U :=
      (Scheme.topologicalKrullDim_eq_orderKrullDim U.toScheme).symm
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, U)) :=
      hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, U) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- If every point has an open neighborhood of Krull dimension at most `d`, then the whole scheme
has Krull dimension at most `d`.

The proof puts each finite specialization chain in a neighborhood of its least element.  Every
other element of the chain is a generization of that point, so it remains in the open set. -/
lemma Scheme.orderKrullDim_le_of_exists_open_orderKrullDim_le (X : Scheme) (d : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Order.krullDim U ≤ d) :
    Order.krullDim X ≤ d := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      rw [Order.krullDim_eq_bot]
      exact bot_le
  | inr hX =>
      let : Nonempty X := hX
      rw [Order.krullDim_eq_iSup_length]
      refine WithBot.coe_le_coe.mpr (iSup_le fun l ↦ ?_)
      obtain ⟨U, hhead, hU⟩ := h l.head
      have hmem (i : Fin (l.length + 1)) : l i ∈ U := by
        have hle : l.head ≤ l i := l.monotone (Fin.zero_le i)
        rw [Scheme.le_iff_specializes] at hle
        exact hle.mem_open U.isOpen hhead
      have hlt (a b : U.toScheme) (hab : U.ι.base a < U.ι.base b) : a < b := by
        rw [lt_iff_le_not_ge]
        constructor
        · rw [Scheme.le_iff_specializes]
          apply U.isOpenEmbedding.isInducing.specializes_iff.mp
          rw [← Scheme.le_iff_specializes]
          exact hab.le
        · intro hback
          apply (not_le_of_gt hab)
          rw [Scheme.le_iff_specializes] at hback ⊢
          exact U.isOpenEmbedding.isInducing.specializes_iff.mpr hback
      let lU : LTSeries U :=
        { length := l.length
          toFun := fun i ↦ ⟨l i, hmem i⟩
          step := fun i ↦ by
            simpa only [Set.mem_ofPred_eq] using
              hlt (⟨l i.castSucc, hmem i.castSucc⟩ : U.toScheme)
                (⟨l i.succ, hmem i.succ⟩ : U.toScheme) (l.step i) }
      have hlength : (l.length : WithBot ℕ∞) ≤ Order.krullDim U :=
        Order.le_krullDim_iff.mpr ⟨lU, rfl⟩
      exact WithBot.coe_le_coe.mp (hlength.trans hU)

variable {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- A smooth complex scheme of relative dimension `d` has order-theoretic Krull dimension at
most `d`. -/
lemma SmoothOfRelativeDimension.orderKrullDim_le_complex
    [SmoothOfRelativeDimension d f] : Order.krullDim X ≤ d := by
  apply Scheme.orderKrullDim_le_of_exists_open_orderKrullDim_le X d
  intro x
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  refine ⟨U, hxU, ?_⟩
  rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU]
  exact (algebraMap_isStandardSmoothOfRelativeDimension
    (d := d) (Over.mk f) hsmooth).ringKrullDim_le_complex

/-- At every point of a smooth complex scheme of relative dimension `d`, the sum of the
order-theoretic dimension and codimension is at most `d`. -/
lemma SmoothOfRelativeDimension.height_add_coheight_le_complex
    [SmoothOfRelativeDimension d f] (x : X) :
    Order.height x + Order.coheight x ≤ d := by
  let : Nonempty X := ⟨x⟩
  have hpoint :
      (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ Order.krullDim X := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : X ↦
      Order.height y + Order.coheight y) x)
  exact WithBot.coe_le_coe.mp
    (hpoint.trans (SmoothOfRelativeDimension.orderKrullDim_le_complex
      (f := f) (d := d)))

/-- If a point of a smooth complex `d`-fold has coheight `p`, its height is at most `d - p`.
This is the direction of the dimension formula that does not require catenarity. -/
lemma SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ} (hx : Order.coheight x = p) :
    Order.height x ≤ d - p := by
  apply ENat.le_sub_of_add_le_right (by simp)
  rw [← hx]
  exact SmoothOfRelativeDimension.height_add_coheight_le_complex
    (f := f) (d := d) x

/-- Every point of a smooth complex scheme of relative dimension `d` has coheight at most `d`. -/
lemma SmoothOfRelativeDimension.coheight_le_complex
    [SmoothOfRelativeDimension d f] (x : X) : Order.coheight x ≤ d := by
  calc
    Order.coheight x ≤ Order.height x + Order.coheight x := le_add_left le_rfl
    _ ≤ d := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := d) x

/-- A smooth complex scheme of relative dimension `d` has no point of coheight `p` when
`d < p`. -/
lemma SmoothOfRelativeDimension.coheight_ne_of_lt
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ} (hp : d < p) :
    Order.coheight x ≠ p := by
  intro hx
  have hle : (p : ℕ∞) ≤ d := by
    rw [← hx]
    exact SmoothOfRelativeDimension.coheight_le_complex (f := f) (d := d) x
  exact (not_le_of_gt (by exact_mod_cast hp)) hle

end AlgebraicGeometry
