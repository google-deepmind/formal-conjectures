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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# The Petersen graph

The **Petersen graph** as the Kneser graph $K(5, 2)$: vertices are the $2$-element subsets of a
$5$-element set, adjacent when disjoint. We record that it has $10$ vertices and is cubic.
-/

namespace SimpleGraph

/-- The vertex type of the Petersen graph: `2`-element subsets of `Fin 5`. -/
abbrev PetersenVertex : Type := {s : Finset (Fin 5) // s.card = 2}

/-- The **Petersen graph** $K(5,2)$: two `2`-subsets of `Fin 5` are adjacent iff disjoint. -/
def petersenGraph : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have hc := s.2
    rw [disjoint_self.mp h] at hc
    simp at hc⟩

instance : DecidableRel petersenGraph.Adj := fun s t =>
  inferInstanceAs (Decidable (Disjoint s.1 t.1))

/-- A canonical vertex `{0, 1}` of the Petersen graph. -/
def petersenVertex01 : PetersenVertex := ⟨{0, 1}, by decide⟩

instance : Nonempty PetersenVertex := ⟨petersenVertex01⟩

/-- The Petersen graph has `10` vertices. -/
theorem card_petersenVertex : Fintype.card PetersenVertex = 10 := by decide

/-- The Petersen graph is cubic. -/
theorem petersenGraph_degree (v : PetersenVertex) : petersenGraph.degree v = 3 := by
  revert v; decide

end SimpleGraph
