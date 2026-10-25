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

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Acyclic vertex colorings
-/

@[expose] public section

namespace SimpleGraph.Coloring

/-- A proper coloring is acyclic when no cycle uses only two colors. -/
def IsAcyclic {V C : Type*} {G : SimpleGraph V} (c : G.Coloring C) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle →
    ¬ ∃ a b : C, ∀ u ∈ w.support, c u = a ∨ c u = b

end SimpleGraph.Coloring
