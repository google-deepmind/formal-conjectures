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

variable {V α ι : Type*} {G : SimpleGraph V} {n : ℕ}

namespace SimpleGraph

/-- An edge coloring of a simple graph `G` with color type `α`.
Note: this exists in upstream Mathlib as SimpleGraph.EdgeLabeling -/
def EdgeColoring (G : SimpleGraph V) (α : Type*) := G.edgeSet → α

variable {W : Type*}

/-- A subgraph `H` of a graph with edge coloring `c` is rainbow if all edges of `H` have distinct
colors. -/
def IsRainbow {V : Type*} {G : SimpleGraph V} {α : Type*} (c : EdgeColoring G α)
    (H : G.Subgraph) : Prop :=
  Function.Injective fun e : H.edgeSet => c ⟨e.val, H.edgeSet_subset e.property⟩

/-- A graph `G` contains a rainbow copy of `H` if there is a subgraph of `G` that is isomorphic
to `H` and is rainbow under the edge coloring `c`. -/
def HasRainbowCopy {V W : Type*} {G : SimpleGraph V} {α : Type*} (c : EdgeColoring G α)
    (H : SimpleGraph W) : Prop :=
  ∃ (S : G.Subgraph), H ⊑ S.coe ∧ IsRainbow c S

/-- An edge coloring of `Kₙ` with `m` colors that avoids rainbow copies of `H`. -/
def IsAntiRamseyColoring (n m : ℕ) (H : SimpleGraph W) : Prop :=
  ∃ (c : EdgeColoring (completeGraph (Fin n)) (Fin m)), ¬HasRainbowCopy c H

/-- The anti-Ramsey number AR(n, H) is the maximum number of colors in which the edges of Kₙ
can be colored without creating a rainbow copy of H. -/
noncomputable def antiRamseyNumber (n : ℕ) (H : SimpleGraph W) : ℕ :=
  sSup {m : ℕ | IsAntiRamseyColoring n m H}

lemma le_chromaticNumber_iff_colorable : n ≤ G.chromaticNumber ↔ ∀ m, G.Colorable m → n ≤ m := by
  simp [chromaticNumber]

lemma le_chromaticNumber_iff_coloring :
    n ≤ G.chromaticNumber ↔ ∀ m, G.Coloring (Fin m) → n ≤ m := by
  simp [le_chromaticNumber_iff_colorable, Colorable]

lemma Coloring.injective_comp_of_pairwise_adj (C : G.Coloring α) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : (C ∘ f).Injective :=
  Function.injective_iff_pairwise_ne.2 fun _i _j hij ↦ C.valid <| hf hij

lemma Colorable.card_le_of_pairwise_adj (hG : G.Colorable n) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : Nat.card ι ≤ n := by
  obtain ⟨C⟩ := hG
  simpa using Nat.card_le_card_of_injective _ (C.injective_comp_of_pairwise_adj f hf)

lemma le_chromaticNumber_of_pairwise_adj (hn : n ≤ Nat.card ι) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : n ≤ G.chromaticNumber :=
  le_chromaticNumber_iff_colorable.2 fun _m hm ↦ hn.trans <| hm.card_le_of_pairwise_adj f hf

instance (f : ι → V) : IsSymm ι fun i j ↦ G.Adj (f i) (f j) where symm _ _ := .symm

variable (G) in
/-- A set of edges is critical if deleting them reduces the chromatic number. -/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

variable (G) in
/-- An edge is critical if deleting it reduces the chromatic number. -/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

/--
A set of vertices is critical if deleting them reduces the chromatic number.
-/
def Subgraph.IsCriticalVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

/--
A vertex is critical if deleting it reduces the chromatic number.
-/
def Subgraph.IsCriticalVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCriticalVerts {v}

variable (G)

/--
A graph `G` is `k`-critical (or vertex-critical) if its chromatic number is `k`,
and deleting any single vertex reduces the chromatic number.
-/
def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCriticalVertex v

theorem not_isCritical_of_fintype_lt [Fintype V] (k : ℕ) (hk : Fintype.card V < k) :
   ¬G.IsCritical k := by
  simp [IsCritical]
  intro h
  have := h ▸ SimpleGraph.chromaticNumber_le_iff_colorable.2 G.colorable_of_fintype
  simp at this
  grind

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

/-- The chromatic cardinal is the minimal number of colors need to color it. In contrast to
`chromaticNumber`, which assigns `⊤ : ℕ∞` to all non-finitely colorable graphs, this definition
returns a `Cardinal` and can therefore distinguish between different infinite chromatic numbers. -/
noncomputable def chromaticCardinal.{u} {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}
