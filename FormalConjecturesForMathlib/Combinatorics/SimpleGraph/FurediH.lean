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
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace SimpleGraph

/-- Index set for the pair-vertices $z_{ij}$ of Füredi's $H_k$, encoded as ordered pairs $i < j$. -/
abbrev FurediH.Pair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/--
Vertices of Füredi's $H_k$: an apex $x$, spokes $y_1,\ldots,y_k$, and a vertex $z_{ij}$ for each
pair $i < j$.
-/
inductive FurediH.Vertex (k : ℕ) where
  | apex : Vertex k
  | spoke : Fin k → Vertex k
  | pair : FurediH.Pair k → Vertex k

/-- Equivalence identifying vertices of $H_k$ with an apex, $k$ spokes, and $\binom{k}{2}$
pair-vertices. -/
def FurediH.Vertex.equivSum (k : ℕ) :
    FurediH.Vertex k ≃ Unit ⊕ Fin k ⊕ FurediH.Pair k where
  toFun
    | .apex => Sum.inl ⟨⟩
    | .spoke i => Sum.inr (Sum.inl i)
    | .pair p => Sum.inr (Sum.inr p)
  invFun
    | .inl _ => .apex
    | .inr (.inl i) => .spoke i
    | .inr (.inr p) => .pair p
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

instance {k : ℕ} : Fintype (FurediH.Vertex k) :=
  Fintype.ofEquiv _ (FurediH.Vertex.equivSum k).symm

/-- The number of pair-vertices of $H_k$ is $\binom{k}{2}$. -/
@[simp]
theorem FurediH.card_pair (k : ℕ) : Fintype.card (FurediH.Pair k) = Nat.choose k 2 := by
  classical
  simp [FurediH.Pair, Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- Cardinality of the vertex set of $H_k$: one apex, $k$ spokes, and $\binom{k}{2}$ pair-vertices. -/
@[simp]
theorem FurediH.card_vertex (k : ℕ) :
    Fintype.card (FurediH.Vertex k) = 1 + k + Nat.choose k 2 := by
  rw [Fintype.card_congr (FurediH.Vertex.equivSum k), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_fin, FurediH.card_pair, Nat.add_assoc]

/--
Adjacency of $H_k$ before `fromRel`: the apex is joined to every $y_i$, and each $z_{ij}$ is joined
to $y_i$ and $y_j$.
-/
def FurediH.adjRel {k : ℕ} : FurediH.Vertex k → FurediH.Vertex k → Prop
  | .apex, .spoke _ => True
  | .spoke a, .pair p => a = p.1.1 ∨ a = p.1.2
  | _, _ => False

/--
Füredi's graph $H_k$: vertices $x,y_1,\ldots,y_k$ and $z_{ij}$ for $i<j$, with $x$ adjacent to every
$y_i$ and each pair $y_i,y_j$ adjacent to the unique vertex $z_{ij}$.
-/
def furediH (k : ℕ) : SimpleGraph (FurediH.Vertex k) :=
  fromRel (FurediH.adjRel (k := k))

/-- The apex is adjacent to every spoke. -/
lemma furediH_adj_apex_spoke {k : ℕ} (i : Fin k) :
    (furediH k).Adj .apex (.spoke i) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- A spoke is adjacent to a pair-vertex precisely when it is one of the pair's endpoints. -/
lemma furediH_adj_spoke_pair {k : ℕ} {i : Fin k} {p : FurediH.Pair k}
    (h : i = p.1.1 ∨ i = p.1.2) :
    (furediH k).Adj (.spoke i) (.pair p) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel, h]

/-- The apex is never adjacent to a pair-vertex. -/
lemma not_furediH_adj_apex_pair {k : ℕ} (p : FurediH.Pair k) :
    ¬ (furediH k).Adj .apex (.pair p) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- Distinct spokes are never adjacent (the $y_i$ form an independent set). -/
lemma not_furediH_adj_spoke_spoke {k : ℕ} (i j : Fin k) :
    ¬ (furediH k).Adj (.spoke i) (.spoke j) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- Pair-vertices are never adjacent to each other. -/
lemma not_furediH_adj_pair_pair {k : ℕ} (p q : FurediH.Pair k) :
    ¬ (furediH k).Adj (.pair p) (.pair q) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

end SimpleGraph
