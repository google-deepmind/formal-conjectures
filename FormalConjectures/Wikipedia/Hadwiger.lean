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
# Hadwiger's conjecture

Hadwiger's conjecture states that every graph with a chromatic number of at least $k$ contains a complete graph on $k$ vertices as a minor. This is a generalization of the four color theorem, which states that every planar graph can be colored with at most four colors.

*References:*

- [Hadwiger's conjecture](https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory))
-/

theorem hadwiger_weaker {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h : k ≤ G.chromaticNumber) : Nonempty (SimpleGraph.Embedding (completeGraph (Fin k)) G) := by
  sorry
