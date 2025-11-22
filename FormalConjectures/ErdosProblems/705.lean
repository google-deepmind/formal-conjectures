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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 705

*Reference:* [erdosproblems.com/705](https://www.erdosproblems.com/705)
-/

namespace Erdos705

open Erdos705

variable {V : Finset (EuclideanSpace ℝ (Fin 2))}

/--
A finite unit distance graph in ℝ^2:
A graph where the vertices are a finite collection of points in ℝ² and there is an edge between
two points if and only if the distance between them is 1.
-/

def unitDistancePlaneGraph (G : SimpleGraph V) : Prop :=
  ∀ x y : V, G.Adj x y ↔ dist x y = 1

/--
Let G be a finite unit distance graph in R².
Is there some k such that if G has girth ≥ k, then χ(G) ≤ 3?
-/

@[category research open, AMS 5]
theorem erdos_705:
  (∀ (G : SimpleGraph V) (h : unitDistancePlaneGraph G),
    ∃ k, SimpleGraph.girth G ≥ k → SimpleGraph.chromaticNumber G ≤ 3) ↔ answer(sorry) := by sorry

end Erdos705
