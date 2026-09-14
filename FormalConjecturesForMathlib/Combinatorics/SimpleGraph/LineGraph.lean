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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Decidable
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Finite line graphs and edge-labeling colorings
-/

@[expose] public section

namespace SimpleGraph

variable {V K : Type*} {G : SimpleGraph V}

instance decidableRelLineGraph [Fintype V] [DecidableEq V] :
    DecidableRel G.lineGraph.Adj := fun _ _ ↦
  decidable_of_iff _ lineGraph_adj_iff_exists.symm

/-- An edge labeling separating incident edges gives a vertex coloring of the line graph. -/
def EdgeLabeling.toLineGraphColoring (c : G.EdgeLabeling K)
    (hc : ∀ v w z (hw : G.Adj v w) (hz : G.Adj v z), w ≠ z →
      c.get v w hw ≠ c.get v z hz) : G.lineGraph.Coloring K :=
  Coloring.mk c (by
    rintro ⟨e, he⟩ ⟨f, hf⟩ h
    obtain ⟨hne, v, hv, hvf⟩ := lineGraph_adj_iff_exists.mp h
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hvf
    apply hc v w z he hf
    intro hwz
    subst z
    exact hne rfl)

/-- Line-graph colorability is precisely the existence of distinct colors on incident edges. -/
theorem lineGraph_colorable_iff (n : ℕ) :
    G.lineGraph.Colorable n ↔ ∃ c : G.EdgeLabeling (Fin n),
      ∀ v w z (hw : G.Adj v w) (hz : G.Adj v z), w ≠ z →
        c.get v w hw ≠ c.get v z hz := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun e ↦ c e, fun v w z hw hz hne ↦ c.valid ?_⟩
    apply lineGraph_adj_iff_exists.mpr
    refine ⟨?_, v, by simp, by simp⟩
    intro he
    exact hne (Sym2.congr_right.mp (congrArg Subtype.val he))
  · rintro ⟨c, hc⟩
    exact ⟨c.toLineGraphColoring hc⟩

end SimpleGraph
