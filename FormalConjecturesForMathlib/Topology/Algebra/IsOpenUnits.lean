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

public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Monoids with open units

Mathlib's `IsOpenUnits M` records that `Mˣ` is open in `M` and carries the subspace topology, but
does not unfold that into the two consequences one actually uses: the units form an open set, and
inversion is continuous on it.

These belong in `Mathlib/Topology/Algebra/IsOpenUnits.lean`; this file can be deleted once they
are there.
-/

@[expose] public section

open Topology

lemma Set.range_units_val {M : Type*} [Monoid M] :
    Set.range (Units.val : Mˣ → M) = {x | IsUnit x} :=
  Set.ext fun _ ↦ ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.isUnit, fun h ↦ ⟨h.unit, h.unit_spec⟩⟩

variable (M : Type*) [Monoid M] [TopologicalSpace M] [IsOpenUnits M]

/-- In a monoid with open units, being a unit is an open condition. -/
lemma isOpen_setOf_isUnit : IsOpen {x : M | IsUnit x} :=
  Set.range_units_val (M := M) ▸ IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range

variable {M} in
/-- Reading off the unit underlying an element known to be one is continuous. -/
lemma continuous_isUnit_unit :
    Continuous fun x : {x : M | IsUnit x} ↦ x.2.unit :=
  IsOpenUnits.isOpenEmbedding_unitsVal.isInducing.continuous_iff.2 <| by
    simpa [Function.comp_def] using continuous_subtype_val

/-- Inversion is continuous on the units of a monoid with zero whose units are open. -/
lemma continuousOn_ringInverse {M : Type*} [MonoidWithZero M] [TopologicalSpace M]
    [IsOpenUnits M] : ContinuousOn (Ring.inverse : M → M) {x | IsUnit x} := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (Units.continuous_coe_inv.comp continuous_isUnit_unit).congr fun x ↦ ?_
  simp [← Ring.inverse_unit x.2.unit]
