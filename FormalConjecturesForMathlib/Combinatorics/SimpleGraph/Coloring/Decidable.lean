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
public import Mathlib.Data.Fintype.Pi

/-!
# Finite decidability of vertex colorability
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A vertex coloring is a function separating adjacent vertices. -/
theorem colorable_iff_exists_color (n : ℕ) :
    G.Colorable n ↔ ∃ c : V → Fin n, ∀ v w, G.Adj v w → c v ≠ c w := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c, fun _ _ h ↦ c.valid h⟩
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c (fun h ↦ hc _ _ h)⟩

/-- Exhaustive finite search for a vertex coloring, without an efficiency claim. -/
instance decidableColorable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (n : ℕ) :
    Decidable (G.Colorable n) :=
  decidable_of_iff _ (G.colorable_iff_exists_color n).symm

end SimpleGraph
