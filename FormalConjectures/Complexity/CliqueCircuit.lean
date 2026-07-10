import FormalConjecturesForMathlib.Complexity.TrapezoidalBitArray
import FormalConjecturesForMathlib.Complexity.NandCircuit
import Mathlib.Data.Finset.Basic

/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

open ComplexityTheory

namespace CliqueCircuit

/-- A graph is represented by its upper triangular adjacency matrix encoded in a bit array. -/
abbrev UndirectedGraphEncoding (n : Nat) :=
  TrapezoidalBitArray n 0

/-- Given an undirected graph, extracts the edge boolean between `u` and `v` where `v < u`. -/
def get_edge {n : Nat} (G : UndirectedGraphEncoding n) (u v : Fin n) (h : v < u) : Bool :=
  TrapezoidalBitArray.get G u ⟨v.val, by omega⟩

/-- The property of a graph containing a k-vertex clique. -/
def hasClique (n k : Nat) (G : UndirectedGraphEncoding n) : Prop :=
  ∃ (s : Finset (Fin n)), s.card = k ∧
    ∀ (u ∈ s) (v ∈ s), (h : v < u) → get_edge G u v h

/-- Property that a NAND circuit correctly detects all k-vertex cliques. -/
def cliqueDetectorCircuit (n k : Nat) (num_gates : ℕ+)
    (circuit : NandCircuit (trapezoid_size n 0) num_gates) : Prop :=
  ∀ (G : UndirectedGraphEncoding n),
    hasClique n k G ↔ eval_circuit (trapezoid_size n 0) num_gates circuit G.bitvec

/-- A circuit has the minimum number of gates if it detects the clique 
    and no smaller circuit can do so. -/
def IsMinCliqueCircuit (n k num_gates : Nat) : Prop :=
  ∃ (h_pos : 0 < num_gates),
    let gates : ℕ+ := ⟨num_gates, h_pos⟩
    (∃ (c : NandCircuit (trapezoid_size n 0) gates), cliqueDetectorCircuit n k gates c) ∧
    (∀ (g : ℕ+) (hg : g.val < num_gates),
      ¬ ∃ (c : NandCircuit (trapezoid_size n 0) g), cliqueDetectorCircuit n k g c)

/--
**Minimum Circuit Size for Clique Detection on Tiny Graphs**:

The exact minimum number of unbounded fan-in NAND gates required to detect 
a 4-vertex clique in an 8-vertex graph. This problem is posed as a miniaturized 
testbed for circuit complexity lower bounds.
-/
@[category research open, AMS 03]
conjecture clique_8_4_bound (c : ℕ) : IsMinCliqueCircuit 8 4 c ↔ c = sorry

end CliqueCircuit
