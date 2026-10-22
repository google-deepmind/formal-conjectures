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

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ContinuousOn

@[expose] public section

open TopologicalSpace

universe u

/-- A metrizable space `X` is an absolute neighborhood retract if every
closed embedding into a metrizable space admits a continuous retraction from an open
neighborhood of its image. -/
class IsAbsoluteNeighborhoodRetract (X : Type u) [TopologicalSpace X] [MetrizableSpace X] :
    Prop where
  exists_neighborhood_retract (Y : Type u) [TopologicalSpace Y] [MetrizableSpace Y] (e : X → Y) :
    Topology.IsClosedEmbedding e → ∃ (U : Set Y), IsOpen U ∧
      ∃ (hU : Set.range e ⊆ U) (r : U → X),
        Continuous r ∧ ∀ x : X, r ⟨e x, hU ⟨x, rfl⟩⟩ = x

/-- The empty space is an absolute neighborhood retract. -/
theorem IsAbsoluteNeighborhoodRetract.of_isEmpty (X : Type u) [TopologicalSpace X]
    [MetrizableSpace X] [IsEmpty X] : IsAbsoluteNeighborhoodRetract X := by
  constructor
  intro Y _ _ e _
  refine ⟨∅, isOpen_empty, ?_, fun y => False.elim y.property, ?_, ?_⟩
  · rintro _ ⟨x, _⟩
    exact isEmptyElim x
  · exact continuous_of_discreteTopology
  · intro x
    exact isEmptyElim x

/-- A nonempty subsingleton space is an absolute neighborhood retract. -/
theorem IsAbsoluteNeighborhoodRetract.of_subsingleton (X : Type u) [TopologicalSpace X]
    [MetrizableSpace X] [Subsingleton X] [Nonempty X] : IsAbsoluteNeighborhoodRetract X := by
  classical
  constructor
  intro Y _ _ e _
  exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ => Classical.arbitrary X,
    continuous_const, fun _ => Subsingleton.elim _ _⟩
