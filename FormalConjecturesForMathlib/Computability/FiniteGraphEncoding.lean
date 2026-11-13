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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.List.GetD

/-!
# Encoded nonempty finite simple graphs

A graph is stored as a vertex count minus one and a row-major Boolean adjacency matrix. The
matrix has the exact required length, is symmetric, and has zero diagonal. The inherited binary
encoding rejects malformed matrices and has a proved decoding round trip. Rational thresholds
can be paired with this encoding using the existing product and rational instances.
-/

@[expose] public section

namespace Computability

/-- Valid adjacency-matrix data for a simple graph on `p.1 + 1` labeled vertices. -/
def IsGraphMatrix (p : ℕ × List Bool) : Prop :=
  p.2.length = (p.1 + 1) * (p.1 + 1) ∧
  (∀ i : Fin (p.1 + 1), p.2.getD (i.val * (p.1 + 1) + i.val) false = false) ∧
  ∀ i j : Fin (p.1 + 1),
    p.2.getD (i.val * (p.1 + 1) + j.val) false =
      p.2.getD (j.val * (p.1 + 1) + i.val) false

instance : DecidablePred IsGraphMatrix := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A nonempty labeled finite graph, represented by its full Boolean adjacency matrix. -/
abbrev FiniteGraph := {p : ℕ × List Bool // IsGraphMatrix p}

namespace FiniteGraph

/-- The number of vertices. -/
def order (G : FiniteGraph) : ℕ := G.val.1 + 1

/-- Labeled vertices of an encoded graph. -/
abbrev Vertex (G : FiniteGraph) := Fin G.order

instance (G : FiniteGraph) : Nonempty G.Vertex := ⟨⟨0, Nat.zero_lt_succ _⟩⟩

/-- The simple graph described by the encoded adjacency matrix. -/
def graph (G : FiniteGraph) : SimpleGraph G.Vertex where
  Adj i j := G.val.2.getD (i.val * G.order + j.val) false = true
  symm := ⟨fun i j h ↦ (G.property.2.2 j i).trans h⟩
  loopless := ⟨fun i h ↦ Bool.false_ne_true ((G.property.2.1 i).symm.trans h)⟩

instance (G : FiniteGraph) : DecidableRel G.graph.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ = true))

private theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (k : Fin n) (a : α) :
    (List.ofFn f).getD k.val a = f k := by
  simp [List.getD_eq_getElem?_getD, k.isLt]

/-- The row-major list of entries of a Boolean square matrix. -/
def adjacencyMatrix (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → Bool) : List Bool :=
  List.ofFn fun k : Fin ((n + 1) * (n + 1)) ↦
    f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

private theorem matrix_get (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → Bool)
    (i j : Fin (n + 1)) :
    (adjacencyMatrix n f).getD (i.val * (n + 1) + j.val) false = f i j := by
  have hval : (finProdFinEquiv (i, j)).val = i.val * (n + 1) + j.val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [← hval]
  unfold adjacencyMatrix
  rw [getD_ofFn]
  simp only [Equiv.symm_apply_apply]

/-- Every simple graph on a positive number of labeled vertices has an adjacency-matrix code. -/
def ofSimpleGraph {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    FiniteGraph :=
  ⟨(n, adjacencyMatrix n fun i j ↦ decide (G.Adj i j)), by
    refine ⟨by simp only [adjacencyMatrix, List.length_ofFn], ?_, ?_⟩
    · intro i
      rw [matrix_get]
      simp
    · intro i j
      rw [matrix_get, matrix_get]
      simp [G.adj_comm]⟩

/-- Reading the native graph back from its adjacency-matrix code preserves every edge. -/
@[simp]
theorem graph_ofSimpleGraph {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    (ofSimpleGraph G).graph = G := by
  ext i j
  change Fin (n + 1) at i j
  change (adjacencyMatrix n fun i j ↦ decide (G.Adj i j)).getD
    (i.val * (n + 1) + j.val) false = true ↔ G.Adj i j
  rw [matrix_get]
  exact decide_eq_true_iff

instance : BitstringEncoding FiniteGraph := BitstringEncoding.ofSubtype

/-- Decoding an encoded graph recovers the exact matrix and all graph data. -/
@[simp]
theorem decode_encode (G : FiniteGraph) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode G) = some G :=
  BitstringEncoding.bitDecode_bitEncode G

/-- Graphs together with a degree parameter and a rational threshold have faithful encodings. -/
@[simp]
theorem decode_encode_threshold (x : FiniteGraph × ℕ × ℚ) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode x) = some x :=
  BitstringEncoding.bitDecode_bitEncode x

end FiniteGraph
end Computability
