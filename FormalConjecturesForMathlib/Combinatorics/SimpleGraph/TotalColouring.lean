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
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Total colourings

A *total colouring* of a simple graph `G` colours both its vertices and its edges so that
adjacent vertices, incident edges, and each vertex with its incident edges all receive distinct
colours. This file defines `SimpleGraph.IsTotalColoring`, `SimpleGraph.TotalColorable` and the
*total chromatic number* `SimpleGraph.totalChromaticNumber`, and proves the trivial upper bound
`|V| + |E|`.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A function `c` on the vertices and edges of `G` (an element of `V ⊕ G.edgeSet`) is a
**total colouring** if adjacent vertices, incident (distinct) edges, and each vertex together
with its incident edges receive different colours. -/
def IsTotalColoring {ι : Type*} (c : V ⊕ G.edgeSet → ι) : Prop :=
  (∀ u v, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
    c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → c (Sum.inl v) ≠ c (Sum.inr e))

/-- `G` is **totally `n`-colourable** if it has a total colouring with `n` colours. -/
def TotalColorable (n : ℕ) : Prop :=
  ∃ c : V ⊕ G.edgeSet → Fin n, G.IsTotalColoring c

/-- The **total chromatic number** `χ''(G)`: the least number of colours in a total colouring. -/
noncomputable def totalChromaticNumber : ℕ :=
  sInf {n | G.TotalColorable n}

/-- Any injective colouring of `V ⊕ G.edgeSet` is a total colouring. -/
theorem isTotalColoring_of_injective {ι : Type*} {c : V ⊕ G.edgeSet → ι}
    (hc : Function.Injective c) : G.IsTotalColoring c :=
  ⟨fun _ _ huv h => G.ne_of_adj huv (Sum.inl_injective (hc h)),
    fun _ _ hef _ h => hef (Sum.inr_injective (hc h)),
    fun _ _ _ h => Sum.inl_ne_inr (hc h)⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- Colouring every vertex and edge differently is a total colouring, so `G` is totally
`|V| + |E|`-colourable. -/
theorem totalColorable_card_add_card :
    G.TotalColorable (Fintype.card V + Fintype.card G.edgeSet) :=
  ⟨fun x => (Fintype.equivFin (V ⊕ G.edgeSet) x).cast (Fintype.card_sum ..),
    G.isTotalColoring_of_injective fun _ _ h =>
      (Fintype.equivFin _).injective (Fin.cast_injective _ h)⟩

/-- The trivial upper bound `χ''(G) ≤ |V| + |E|`. -/
theorem totalChromaticNumber_le_card_add_card :
    G.totalChromaticNumber ≤ Fintype.card V + Fintype.card G.edgeSet :=
  Nat.sInf_le G.totalColorable_card_add_card

end SimpleGraph
