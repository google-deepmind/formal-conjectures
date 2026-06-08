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

public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

/-!
# Edge colourings of a SimpleGraph

`SimpleGraph.IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of
the edges of `H` into colour classes indexed by `ι`. The classes must (1) cover `H`
(`H = ⨆ i, c i`) and (2) be pairwise disjoint (each edge belongs to exactly one class).

This unifies the previous local `IsNEdgeColouring` (`ι = Fin n`) and `IsCountableEdgeColouring`
(`ι = ℕ`) shapes used in `FormalConjectures/ErdosProblems/596.lean`. The two are now special
cases of `IsEdgeColouring` parameterised by the index type.
-/

namespace SimpleGraph

/-- `IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of the edges
of `H`: the colour classes cover `H` (`H = ⨆ i, c i`) and are pairwise disjoint. -/
def IsEdgeColouring {V ι : Type*} (H : SimpleGraph V) (c : ι → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

end SimpleGraph
