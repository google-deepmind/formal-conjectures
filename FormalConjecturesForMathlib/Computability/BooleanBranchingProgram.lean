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

public import FormalConjecturesForMathlib.Computability.BooleanTruthTable

/-!
# Finite deterministic Boolean branching programs

Nodes 0 and 1 are the two sinks. Query nodes are topologically numbered from 2
upwards, and both edges of a query point to smaller indices. The last node is
the unique source: every other node has an incoming edge. Size includes both
sinks. Queries may repeat, and there is no ordering or read-once restriction.

This is the literal graph convention of Glinskih–Riazanov, *Partial Minimum
Branching Program Size Problem Is ETH-Hard*, §2, pp. 54:5–54:6:
https://doi.org/10.4230/LIPIcs.ITCS.2025.54.
In particular, an unused sink is not permitted. Evaluation follows edges by
well-founded recursion on node indices, without an arbitrary fuel bound.
-/

@[expose] public section

namespace BooleanBranchingProgram

/-- An acyclic binary branching program with exactly one source and two sinks. -/
structure Program (n : ℕ) where
  /-- The number of query nodes, excluding the two sinks. -/
  count : ℕ
  nonempty : 0 < count
  query : Fin count → Fin n
  low : Fin count → Fin (count + 2)
  high : Fin count → Fin (count + 2)
  low_lt : ∀ q, (low q).val < q.val + 2
  high_lt : ∀ q, (high q).val < q.val + 2
  incoming : ∀ i : Fin (count + 2), i.val < count + 1 →
    ∃ q, low q = i ∨ high q = i

namespace Program

/-- All nodes, including the two sinks, contribute to size. -/
def size {n : ℕ} (p : Program n) : ℕ := p.count + 2

/-- The unique source is the last node. -/
def root {n : ℕ} (p : Program n) : Fin (p.count + 2) :=
  ⟨p.count + 1, by omega⟩

/-- The directed graph underlying a program (forgetting the labels on parallel edges). -/
def Edge {n : ℕ} (p : Program n) (i j : Fin (p.count + 2)) : Prop :=
  ∃ q : Fin p.count, i.val = q.val + 2 ∧ (p.low q = j ∨ p.high q = j)

theorem edge_lt {n : ℕ} (p : Program n) {i j : Fin (p.count + 2)}
    (h : p.Edge i j) : j.val < i.val := by
  obtain ⟨q, hi, hq⟩ := h
  rcases hq with rfl | rfl
  · simpa [hi] using p.low_lt q
  · simpa [hi] using p.high_lt q

theorem no_incoming_iff_root {n : ℕ} (p : Program n) (i : Fin (p.count + 2)) :
    (¬ ∃ j, p.Edge j i) ↔ i = p.root := by
  constructor
  · intro h
    apply Fin.ext
    by_contra hi
    have hi' : i.val < p.count + 1 := by
      have := i.isLt
      simp only [root] at hi
      omega
    obtain ⟨q, hq⟩ := p.incoming i hi'
    exact h ⟨⟨q.val + 2, by have := q.isLt; omega⟩, q, rfl, hq⟩
  · rintro rfl ⟨j, hj⟩
    have := p.edge_lt hj
    have := j.isLt
    simp only [root] at *
    omega

theorem no_outgoing_iff_sink {n : ℕ} (p : Program n) (i : Fin (p.count + 2)) :
    (¬ ∃ j, p.Edge i j) ↔ i.val < 2 := by
  constructor
  · intro h
    by_contra hi
    have hq : i.val - 2 < p.count := by have := i.isLt; omega
    let q : Fin p.count := ⟨i.val - 2, hq⟩
    exact h ⟨p.low q, q, by dsimp [q]; omega, Or.inl rfl⟩
  · rintro hi ⟨j, q, hq, _⟩
    omega

/-- Follow the edge selected by the queried input bit. -/
def next {n : ℕ} (p : Program n) (v : Fin n → Bool)
    (i : Fin (p.count + 2)) (hi : 2 ≤ i.val) : Fin (p.count + 2) :=
  let q : Fin p.count := ⟨i.val - 2, by have := i.isLt; omega⟩
  if v (p.query q) then p.high q else p.low q

theorem next_lt {n : ℕ} (p : Program n) (v : Fin n → Bool)
    (i : Fin (p.count + 2)) (hi : 2 ≤ i.val) : (p.next v i hi).val < i.val := by
  dsimp [next]
  split
  · have := p.high_lt ⟨i.val - 2, by have := i.isLt; omega⟩
    dsimp only at this
    omega
  · have := p.low_lt ⟨i.val - 2, by have := i.isLt; omega⟩
    dsimp only at this
    omega

/-- Path semantics: stop at a sink, otherwise recurse along the selected edge. -/
def evalNode {n : ℕ} (p : Program n) (v : Fin n → Bool) (i : Fin (p.count + 2)) : Bool :=
  if hi : i.val < 2 then i.val == 1
  else p.evalNode v (p.next v i (by omega))
termination_by i.val
decreasing_by exact p.next_lt v i _

/-- Evaluate from the unique source. -/
def eval {n : ℕ} (p : Program n) (v : Fin n → Bool) : Bool :=
  p.evalNode v p.root

@[simp]
theorem evalNode_zero {n : ℕ} (p : Program n) (v : Fin n → Bool) :
    p.evalNode v ⟨0, by omega⟩ = false := by
  rw [evalNode]
  rfl

@[simp]
theorem evalNode_one {n : ℕ} (p : Program n) (v : Fin n → Bool) :
    p.evalNode v ⟨1, by omega⟩ = true := by
  rw [evalNode]
  rfl

theorem three_le_size {n : ℕ} (p : Program n) : 3 ≤ p.size := by
  have := p.nonempty
  dsimp [size]
  omega

/-- With the literal two-sink/one-source convention, zero inputs admit no program. -/
theorem not_nonempty_zero : ¬ Nonempty (Program 0) := by
  rintro ⟨p⟩
  exact Fin.elim0 (p.query ⟨0, p.nonempty⟩)

end Program

end BooleanBranchingProgram
