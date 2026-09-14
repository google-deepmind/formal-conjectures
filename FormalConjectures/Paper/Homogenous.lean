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

import FormalConjecturesUtil

/-!
# Conjectures around homogeneous topological spaces

This file formalizes the notions of a homogeneous topological space and of (ω-)monolithic
topological spaces, and states some open problems about homogeneous and monolithic compact spaces.

*References:*
* [Ar2013] Arhangeliski, Alexandr. "Selected old open problems in general topology."
  Buletinul Academiei de Ştiinţe a Republicii Moldova. Matematica 73.2-3 (2013): 37-46.
  https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf
* [Ar1987] Arhangel'skii, A. V. "Topological homogeneity. Topological groups and their continuous
  images." Russian Mathematical Surveys 42.2 (1987): 83-131.
  https://doi.org/10.1070/RM1987v042n02ABEH001333
-/

open TopologicalSpace Topology Filter Set
open scoped Cardinal

namespace Homogeneous

/--
A topological space $X$ is called *homogeneous* if for all $x, y \in X$ there is homeomorphism
$f : X \to X$ with $f(x) = y$.
-/
class HomogeneousSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_equiv : ∀ x y : X, ∃ f : X ≃ₜ X, f x = y

/-- Every discrete space is homogeneous. -/
@[category test, AMS 54]
instance DiscreteTopology.toHomogeneousSpace (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    HomogeneousSpace X where
  exists_equiv x y := by
    classical
    use IsHomeomorph.homeomorph (Equiv.swap x y)
      (IsHomeomorph.equiv_of_discreteTopology (Equiv.swap x y))
    rw [IsHomeomorph.homeomorph_apply, Equiv.swap_apply_left]

/-- Problem 13 in [Ar2013]:
Is it true that every infinite homogeneous compact hausdorff
space contains a non-trivial convergent sequence? -/
@[category research open, AMS 54]
theorem homogeneousSpace_exists_inj_tendsto :
    answer(sorry) ↔ ∀ (X : Type) (_ : TopologicalSpace X), ¬ Finite X → T2Space X → CompactSpace X →
      HomogeneousSpace X → ∃ s : ℕ → X, s.Injective ∧ ∃ a : X, Tendsto s atTop (nhds a) := by
  sorry

/-- Problem 14 in [Ar2013]:
Is it possible to represent an arbitrary compact hausdorff space as an image
of a homogeneous compact space under a continuous mapping? -/
@[category research open, AMS 54]
theorem homogeneousSpace_exists_surjective :
    answer(sorry) ↔ ∀ (X : Type) (_ : TopologicalSpace X), T2Space X → CompactSpace X →
      ∃ (Y : Type) (_ : TopologicalSpace Y), T2Space Y ∧ CompactSpace Y ∧ HomogeneousSpace Y ∧
        ∃ f : Y → X, Continuous f ∧ f.Surjective := by
  sorry

/-- A topological space is called ω-monolithic if
the closure of every countable subspace is metrizable. -/
class CountablyMonolithicSpace (X : Type*) [TopologicalSpace X] : Prop where
  metrizable_of_closure_of_countable : ∀ ⦃s : Set X⦄, s.Countable → MetrizableSpace (closure s)

/-- Every Metrizable space is ω-monolithic. -/
@[category test, AMS 54]
instance MetrizableSpace.countablyMonolithicSpace
    (X : Type*) [TopologicalSpace X] [MetrizableSpace X] : CountablyMonolithicSpace X := by
  refine { metrizable_of_closure_of_countable := ?_ }
  intros
  infer_instance

/-- Problem 15 in [Ar2013]:
Is every homogeneous ω-monolithic compact hausdorff space first countable? -/
@[category research open, AMS 54]
theorem firstCountableTopology_of_countablyMonolithicSpace :
    answer(sorry) ↔ ∀ (X : Type) (_ : TopologicalSpace X), T2Space X → CompactSpace X →
      HomogeneousSpace X → CountablyMonolithicSpace X → FirstCountableTopology X := by
  sorry

/-- Problem 16 in [Ar2013]:
Is the cardinality of every homogeneous ω-monolithic compact hausdorff space not greater than 𝔠? -/
@[category research open, AMS 54]
theorem countablyMonolithicSpace_card_lt :
    answer(sorry) ↔ ∀ (X : Type) (_ : TopologicalSpace X), T2Space X → CompactSpace X →
      HomogeneousSpace X → CountablyMonolithicSpace X → #X ≤ 𝔠 := by
  sorry

/-- A topological space `X` is *monolithic* (see [Ar1987]; [Ar2013] uses the term without
defining it) if for every infinite cardinal `κ`, every subspace of `X` of density at most `κ` has
network weight at most `κ`. -/
class MonolithicSpace (X : Type*) [TopologicalSpace X] : Prop where
  networkWeight_le_of_density_le :
    ∀ ⦃κ : Cardinal⦄, ℵ₀ ≤ κ → ∀ ⦃Y : Set X⦄, density Y ≤ κ → networkWeight Y ≤ κ

/-- A space is monolithic iff `nw(cl A) ≤ |A| + ω` for every subset `A`, the other standard
formulation of monolithicity. -/
@[category test, AMS 54]
theorem monolithicSpace_iff_networkWeight_closure_le (X : Type*) [TopologicalSpace X] :
    MonolithicSpace X ↔ ∀ s : Set X, networkWeight (closure s) ≤ max #s ℵ₀ := by
  constructor
  · intro h s
    refine h.networkWeight_le_of_density_le (le_max_right _ _) ?_
    have hd : Dense ((↑) ⁻¹' s : Set (closure s)) := by
      rw [Subtype.dense_iff, Subtype.image_preimage_coe, inter_eq_right.mpr subset_closure]
    exact hd.density_le.trans
      ((Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective).trans (le_max_left _ _))
  · intro h
    refine ⟨fun κ hκ Y hY => ?_⟩
    obtain ⟨D, hD, hD'⟩ := exists_dense_mk_eq_density (X := Y)
    have hsub : Y ⊆ closure (Subtype.val '' D) := Subtype.dense_iff.mp hD
    calc networkWeight Y
        ≤ networkWeight (closure (Subtype.val '' D)) :=
          (IsEmbedding.inclusion hsub).isInducing.networkWeight_le
      _ ≤ max #(Subtype.val '' D) ℵ₀ := h _
      _ = max #D ℵ₀ := by rw [Cardinal.mk_image_eq Subtype.val_injective]
      _ ≤ κ := max_le (hD'.trans_le hY) hκ

/-- Every discrete space is monolithic. -/
@[category test, AMS 54]
instance DiscreteTopology.toMonolithicSpace (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    MonolithicSpace X where
  networkWeight_le_of_density_le _ _ _ hY := by rwa [networkWeight_eq_mk, ← density_eq_mk]

/-- Every second countable space is monolithic. -/
@[category test, AMS 54]
instance SecondCountableTopology.toMonolithicSpace (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] : MonolithicSpace X where
  networkWeight_le_of_density_le _ hκ _ _ := networkWeight_le_aleph0.trans hκ

/-- Problem 17 in [Ar2013]:
Is it true that every nonempty monolithic compact hausdorff space contains a point with a
first countable neighborhood basis?

Note: `Nonempty X` is required since the conclusion asserts the existence of a point.
-/
@[category research open, AMS 54]
theorem monolithicSpace_exists_nhds_generated_countable :
    answer(sorry) ↔ ∀ (X : Type) (_ : TopologicalSpace X), T2Space X → CompactSpace X →
      Nonempty X → MonolithicSpace X → ∃ x : X, (𝓝 x).IsCountablyGenerated := by
  sorry

end Homogeneous
