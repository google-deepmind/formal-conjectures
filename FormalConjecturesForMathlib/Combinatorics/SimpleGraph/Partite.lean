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

/-!
# Graphs with fixed parts
-/

@[expose] public section

namespace SimpleGraph

/--
A graph on `Fin r × Fin n` is `r`-partite with parts `{i} × Fin n` (each of size `n`) if
there are no edges inside a part.
-/
def IsPartite {ι α : Type*} (G : SimpleGraph (ι × α)) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x.1 ≠ y.1

/-- The graph with no edges respects every fixed partition. -/
theorem isPartite_bot {ι α : Type*} : IsPartite (⊥ : SimpleGraph (ι × α)) := by
  intro x y h
  exact h.elim

end SimpleGraph
