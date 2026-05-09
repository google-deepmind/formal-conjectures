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

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homeomorph

@[expose] public section

/-- A space is homogeneous if its homeomorphism group acts transitively. -/
class HomogeneousSpace (X : Type*) [TopologicalSpace X] : Prop where
  is_transitive : ∀ x y : X, ∃ f : Homeomorph X X, f x = y
