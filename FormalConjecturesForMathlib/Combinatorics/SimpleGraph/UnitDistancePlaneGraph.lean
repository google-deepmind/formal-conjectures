/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical Finset List

/-- A unit distance graph in ℝ²:
A graph where the vertices V are a collection of points in ℝ² and there is
an edge between two points if and only if the distance between them is 1. -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := Dist.dist x y = 1
  symm x y := by simp [PseudoMetricSpace.dist_comm]



end SimpleGraph
