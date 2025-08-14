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

import Mathlib


universe u

open Classical

variable {V : Type u}

open SimpleGraph
namespace SimpleGraph

theorem Colorable_iff_induce_bot (G : SimpleGraph V) (n : ℕ) : G.Colorable n ↔ ∃ coloring : V → Fin n,
  ∀ i, G.induce {v | coloring v = i} = ⊥ := by
  constructor
  · intro ⟨a, h⟩
    use a
    intro i
    aesop
  · intro ⟨w, h⟩
    use w
    intro a b h_adj
    by_contra hw
    absurd h
    push_neg
    use w a
    by_contra hG
    have : ¬ ((SimpleGraph.induce {v | w v = w a} G).Adj ⟨a, by rfl⟩ ⟨b, by simp_all⟩) := by
      rw [hG]
      simp
    exact hw fun a ↦ this h_adj

def Cocolorable (G : SimpleGraph V) (n : ℕ) : Prop := ∃ coloring : V → Fin n,
  ∀ i, letI induced_color_class := G.induce {v | coloring v = i}
  induced_color_class = ⊥ ∨ induced_color_class = ⊤

example (G : SimpleGraph V) (n : ℕ) : G.Colorable n → SimpleGraph.Cocolorable G n := by
  simp [Colorable_iff_induce_bot, Cocolorable]
  aesop

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chromatic number. -/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ setOf G.Cocolorable, (n : ℕ∞)
