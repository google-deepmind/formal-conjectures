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

public import FormalConjecturesForMathlib.Computability.NetworkProblems
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Partition.Finpartition

/-!
# Encoded graph partition and balanced biclique problems

Finite partitions have nonempty, pairwise disjoint parts covering all vertices. Clique
partition has an input bound on the number of parts; triangle partition has exactly three
vertices in every part. Weighted graph partition has no bound on the number of parts.
Crossing edges are counted once, in increasing vertex order, and nonedge weights are ignored.

The inputs use the existing list, pair, Boolean, and binary natural-number encodings.
The finite decision instances are exhaustive reference checks, not polynomial algorithms.

References: Garey and Johnson, *Computers and Intractability* (1979), GT11, GT15, GT24,
ND14, ND17; Theorem 3.7 (pp. 68–69) specifies a positive number of triangles.
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
-/

@[expose] public section

namespace Computability.GraphPartitionProblems

open MatrixGraph NetworkProblems

/-- A genuine partition of the entire explicitly encoded vertex set. -/
abbrev VertexPartition (a : Code) := Finpartition (Finset.univ : Finset (Fin a.length))

/-- GT15: partition the vertices into at most a positive input number of cliques. -/
def CliquePartition (input : Code × ℕ) : Prop :=
  ValidGraph input.1 ∧ 0 < input.2 ∧ input.2 ≤ input.1.length ∧
    ∃ p : VertexPartition input.1, p.parts.card ≤ input.2 ∧
      ∀ s ∈ p.parts, (toGraph input.1).IsClique s

/-- GT11, with the positive-size convention of Theorem 3.7: partition all vertices into
triangles. The divisibility condition explicitly rejects malformed vertex counts. -/
def TrianglePartition (a : Code) : Prop :=
  ValidGraph a ∧ 0 < a.length ∧ 3 ∣ a.length ∧
    ∃ p : VertexPartition a, ∀ s ∈ p.parts, s.card = 3 ∧ (toGraph a).IsClique s

instance (input : Code × ℕ) : Decidable (CliquePartition input) := by
  unfold CliquePartition
  infer_instance

instance (a : Code) : Decidable (TrianglePartition a) := by
  unfold TrianglePartition
  infer_instance

/-- The number of triangles is forced by the partition, not just bounded above. -/
theorem triangle_parts_card {a : Code} (p : VertexPartition a)
    (h : ∀ s ∈ p.parts, s.card = 3) : 3 * p.parts.card = a.length := by
  have hs := p.sum_card_parts
  rw [Finset.sum_congr rfl h] at hs
  simpa [Nat.mul_comm] using hs

/-- GT24: a bipartite graph containing a balanced complete bipartite subgraph with
exactly the positive input number of vertices on each side. -/
def BalancedBiclique (input : Code × ℕ) : Prop :=
  Colorable (input.1, 2) ∧ 0 < input.2 ∧ input.2 ≤ input.1.length ∧
    ∃ left right : Finset (Fin input.1.length),
      left.card = input.2 ∧ right.card = input.2 ∧
      ∀ u ∈ left, ∀ v ∈ right, (toGraph input.1).Adj u v

instance (input : Code × ℕ) : Decidable (BalancedBiclique input) := by
  unfold BalancedBiclique
  infer_instance

/-- Cross adjacency forces disjoint sides because the graph has no loops. -/
theorem biclique_sides_disjoint {a : Code} {left right : Finset (Fin a.length)}
    (h : ∀ u ∈ left, ∀ v ∈ right, (toGraph a).Adj u v) : Disjoint left right := by
  rw [Finset.disjoint_left]
  intro u hl hr
  exact (toGraph a).loopless.irrefl u (h u hl u hr)

/-- The finite witness is exactly a Mathlib copy of the balanced complete bipartite graph. -/
theorem balancedBiclique_iff (a : Code) (k : ℕ) :
    BalancedBiclique (a, k) ↔ ValidGraph a ∧ (toGraph a).IsBipartite ∧
      0 < k ∧ k ≤ a.length ∧
      SimpleGraph.IsContained (completeBipartiteGraph (Fin k) (Fin k)) (toGraph a) := by
  simp only [BalancedBiclique, colorable_iff, SimpleGraph.IsBipartite,
    SimpleGraph.completeBipartiteGraph_isContained_iff, Fintype.card_fin]
  simp only [SimpleGraph.IsCompleteBetween, Finset.mem_coe]
  tauto

/-- Actual edges whose endpoints have different labels, in canonical orientation. -/
def crossingEdges {β : Type*} [DecidableEq β] (a : Code) (label : Fin a.length → β) :
    Finset (Fin a.length × Fin a.length) :=
  Finset.univ.filter fun e ↦ e.1 < e.2 ∧ entry a e.1 e.2 = true ∧ label e.1 ≠ label e.2

theorem mem_crossingEdges {β : Type*} [DecidableEq β] (a : Code)
    (label : Fin a.length → β) (u v : Fin a.length) :
    (u, v) ∈ crossingEdges a label ↔
      u < v ∧ entry a u v = true ∧ label u ≠ label v := by
  simp [crossingEdges]

/-- Nonnegative total weight, with every crossing undirected edge counted exactly once. -/
def crossingWeight {β : Type*} [DecidableEq β] (a : Code) (w : List (List ℕ))
    (label : Fin a.length → β) : ℕ :=
  ∑ e ∈ crossingEdges a label, weight w e.1.val e.2.val

/-- Relabeling parts injectively does not change which edges cross. -/
theorem crossingEdges_relabel {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (a : Code) (label : Fin a.length → β) (f : β → γ) (hf : Function.Injective f) :
    crossingEdges a (f ∘ label) = crossingEdges a label := by
  ext e
  simp [crossingEdges, hf.eq_iff]

theorem crossingWeight_relabel {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (a : Code) (w : List (List ℕ)) (label : Fin a.length → β)
    (f : β → γ) (hf : Function.Injective f) :
    crossingWeight a w (f ∘ label) = crossingWeight a w label := by
  simp only [crossingWeight, crossingEdges_relabel a label f hf]

/-- Graph, vertex weights, symmetric edge-weight matrix, capacity, and crossing budget. -/
abbrev WeightedPartitionInput := Code × (List ℕ × (List (List ℕ) × (ℕ × ℕ)))

/-- ND14: positive vertex and edge weights, positive per-part capacity and crossing budget.
No connectivity, balance, or fixed number of parts is required. -/
def WeightedPartition (input : WeightedPartitionInput) : Prop :=
  let a := input.1
  let vertices := input.2.1
  let w := input.2.2.1
  let capacity := input.2.2.2.1
  let budget := input.2.2.2.2
  ValidGraph a ∧ vertices.length = a.length ∧ (∀ v ∈ vertices, 0 < v) ∧
    WeightMatrix w a.length ∧
    (∀ u v : Fin a.length, entry a u v = true → 0 < weight w u.val v.val) ∧
    0 < capacity ∧ 0 < budget ∧ ∃ p : VertexPartition a,
      (∀ s ∈ p.parts, (∑ v ∈ s, (vertices[v.val]?).getD 0) ≤ capacity) ∧
      crossingWeight a w p.part ≤ budget

instance (input : WeightedPartitionInput) : Decidable (WeightedPartition input) := by
  unfold WeightedPartition
  infer_instance

/-- Graph, symmetric edge-weight matrix, terminal indices, size bound, budget. -/
abbrev BoundedCutInput := Code × (List (List ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

/-- ND17: positive edge weights; separate the terminals with both sides bounded in size and crossing
weight bounded above. A side and its complement partition all vertices. Invalid terminal
indices, coincident terminals, and zero or excessive size bounds cannot be accepted. -/
def BoundedCut (input : BoundedCutInput) : Prop :=
  let a := input.1
  let w := input.2.1
  let terminals := input.2.2.1
  let bound := input.2.2.2.1
  let budget := input.2.2.2.2
  ValidGraph a ∧ WeightMatrix w a.length ∧
    (∀ u v : Fin a.length, entry a u v = true → 0 < weight w u.val v.val) ∧
    0 < bound ∧ bound ≤ a.length ∧ 0 < budget ∧
    ∃ (s t : Fin a.length) (left : Finset (Fin a.length)),
      s.val = terminals.1 ∧ t.val = terminals.2 ∧ s ∈ left ∧ t ∉ left ∧
      left.card ≤ bound ∧ leftᶜ.card ≤ bound ∧
      crossingWeight a w (fun v ↦ decide (v ∈ left)) ≤ budget

instance (input : BoundedCutInput) : Decidable (BoundedCut input) := by
  unfold BoundedCut
  infer_instance

/-- Complementary sides cover every vertex and never overlap. -/
theorem cut_partition {n : ℕ} (left : Finset (Fin n)) :
    Disjoint left leftᶜ ∧ left ∪ leftᶜ = Finset.univ := by
  exact ⟨disjoint_compl_right, Finset.union_compl left⟩

/-- The two size bounds jointly constrain the entire graph. -/
theorem cut_size_bound {n bound : ℕ} (left : Finset (Fin n))
    (hl : left.card ≤ bound) (hr : leftᶜ.card ≤ bound) : n ≤ 2 * bound := by
  have hc := Finset.card_add_card_compl left
  simp only [Fintype.card_fin] at hc
  omega

end Computability.GraphPartitionProblems
