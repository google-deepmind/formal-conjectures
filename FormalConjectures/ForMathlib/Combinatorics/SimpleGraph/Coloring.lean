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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.CompletePartialOrder

universe u

open Classical

variable {V : Type u} (G : SimpleGraph V)

namespace SimpleGraph

/--
A set of edges is critical  if deleting them reduces the chromatic number.
-/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

/--
An edge is critical if deleting it reduces the chromatic number.
-/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

variable {G}

/--
A set of vertices is critical if deleting them reduces the chromatic number.
-/
def Subgraph.IsCritialVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

/--
A vertex is critical if deleting it reduces the chromatic number.
-/
def Subgraph.IsCritialVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCritialVerts {v}

variable (G)

/--
A graph `G` is `k`-critical (or vertex-critical) if its chromatic number is `k`,
and deleting any single vertex reduces the chromatic number.
-/
def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCritialVertex v


open SimpleGraph

theorem colorable_iff_induce_eq_bot (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔ ∃ coloring : V → Fin n, ∀ i, G.induce {v | coloring v = i} = ⊥ := by
  refine ⟨fun ⟨a, h⟩ ↦ ⟨a, by aesop⟩, fun ⟨w, h⟩ ↦ ⟨w, @fun a b h_adj ↦ ?_⟩⟩
  specialize h (w a)
  contrapose h
  intro hG
  have : ¬ ((SimpleGraph.induce {v | w v = w a} G).Adj ⟨a, by rfl⟩ ⟨b, by simp_all⟩) :=
    hG ▸ fun a ↦ a
  exact this h_adj

def Cocolorable (G : SimpleGraph V) (n : ℕ) : Prop := ∃ coloring : V → Fin n,
  ∀ i, G.induce {v | coloring v = i} = ⊥ ∨ G.induce {v | coloring v = i} = ⊤

example (G : SimpleGraph V) (n : ℕ) : G.Colorable n → SimpleGraph.Cocolorable G n := by
  simp [colorable_iff_induce_eq_bot, Cocolorable]
  aesop

/--
The chromatic number of a graph is the minimal number of colors needed to color it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chromatic number.
-/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ setOf G.Cocolorable, (n : ℕ∞)
