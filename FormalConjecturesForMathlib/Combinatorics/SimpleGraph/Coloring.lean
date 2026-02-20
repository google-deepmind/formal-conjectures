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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card

variable {V α ι : Type*} {G : SimpleGraph V} {n : ℕ}

namespace SimpleGraph

@[inherit_doc] scoped notation "χ(" G ")" => chromaticNumber G

lemma le_chromaticNumber_iff_colorable : n ≤ G.chromaticNumber ↔ ∀ m, G.Colorable m → n ≤ m := by
  simp [chromaticNumber]

lemma le_chromaticNumber_iff_coloring :
    n ≤ G.chromaticNumber ↔ ∀ m, G.Coloring (Fin m) → n ≤ m := by
  simp [le_chromaticNumber_iff_colorable, Colorable]

lemma lt_chromaticNumber_iff_not_colorable : n < G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [← chromaticNumber_le_iff_colorable, not_le]

lemma le_chromaticNumber_iff_not_colorable (hn : n ≠ 0) :
    n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

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

lemma card_div_indepNum_le_chromaticNumber : ⌈(Nat.card V / α(G) : ℚ≥0)⌉₊ ≤ G.chromaticNumber := by
  cases finite_or_infinite V
  swap; · simp
  cases nonempty_fintype V
  simp only [Nat.card_eq_fintype_card, le_chromaticNumber_iff_coloring, Nat.ceil_le]
  refine fun m c ↦ div_le_of_le_mul₀ (by simp) (by simp) ?_
  norm_cast
  rw [← mul_one (Fintype.card V), ← Fintype.card_fin m]
  refine Finset.card_mul_le_card_mul (c · = ·)
    (by simp [Finset.bipartiteAbove, Finset.filter_nonempty_iff])
    fun b _ ↦ IsIndepSet.card_le_indepNum ?_
  simpa [IsIndepSet, Set.Pairwise] using fun x hx y hy _ ↦ c.not_adj_of_mem_colorClass hx hy

instance (f : ι → V) : Std.Symm fun i j ↦ G.Adj (f i) (f j) where symm _ _ := .symm

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

/-- The maximum size of the union of k finite independent sets. -/
noncomputable def indepNumK (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup {n | ∃ f : Fin k → Set V, (∀ i, G.IsIndepSet (f i)) ∧ (⋃ i, f i).ncard = n}

/-- A finite graph is CDS-colorable if it has a proper coloring
by natural numbers such that for all `k > 0`, the number of
vertices with color `< k` equals the maximum size of
the union of `k` independent sets. -/
def CDSColorable [Fintype α] {G : SimpleGraph α} : Prop :=
    ∃ (C : G.Coloring Nat), ∀ k : Nat,
   ∑ i < k, (C.colorClass i).ncard = indepNumK G k

/-- A homomorphism is rainbow if it maps distinct edges to distinct colors. -/
def IsRainbow {α V : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G) {C : Type*}
    (c : Sym2 V → C) : Prop :=
  Function.Injective fun e : H.edgeSet => c (Sym2.map f e)

/--
The anti-Ramsey number $\mathrm{AR}(n, H)$: maximum colors to edge-color $K_n$ without rainbow $H$.
-/
noncomputable def antiRamseyNum {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {k | ∃ c : Sym2 (Fin n) → Fin k, ∀ f : H →g ⊤, ¬IsRainbow f c}
