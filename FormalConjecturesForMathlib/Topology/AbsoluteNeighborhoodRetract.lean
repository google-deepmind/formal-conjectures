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
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.ContinuousOn

@[expose] public section

/--
A topological space `X` is an *absolute neighborhood retract* (ANR) if, whenever it is
embedded as a closed subspace of a normal space `Y`, there exists a continuous retraction
from some open neighborhood of `X` in `Y` onto `X`.

More precisely, for every closed embedding `e : X → Y` into a normal space `Y`, there
exist an open set `U ⊆ Y` containing the image of `e` and a continuous map `r : Y → X`
defined on `U` such that `r ∘ e = id`.
-/
class IsAbsoluteNeighborhoodRetract (X : Type*) [TopologicalSpace X] : Prop where
  exists_neighborhood_retract : ∀ (Y : Type _) [TopologicalSpace Y] [NormalSpace Y] (e : X → Y), Topology.IsClosedEmbedding e →
  ∃ (U : Set Y) (r : Y → X), IsOpen U ∧ Set.range e ⊆ U ∧ ContinuousOn r U ∧ ∀ x : X, r (e x) = x
