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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Homogeneous sets and Ramsey graphs

A homogeneous vertex set is a clique or an independent set. A finite graph is `C`-Ramsey if
every homogeneous set has at most `C * log n` vertices, where `log` is the natural logarithm.

## References

* B. Bukh and B. Sudakov, *Induced subgraphs of Ramsey graphs with many distinct degrees*,
  J. Combin. Theory Ser. B 97 (2007), 612–619.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t : Set V}

/-- A vertex set is homogeneous if it is a clique or an independent set. -/
def IsHomogeneous (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsClique s ∨ G.IsIndepSet s

theorem IsHomogeneous.subset (h : t ⊆ s) : G.IsHomogeneous s → G.IsHomogeneous t := by
  intro hs
  exact hs.imp (IsClique.subset h) (fun hi ↦
    G.isClique_compl.mp (IsClique.subset h (G.isClique_compl.mpr hi)))

@[simp] theorem isHomogeneous_empty : G.IsHomogeneous ∅ :=
  Or.inl G.isClique_empty

@[simp] theorem isHomogeneous_singleton (v : V) : G.IsHomogeneous {v} :=
  Or.inl (G.isClique_singleton v)

@[simp] theorem isHomogeneous_compl : Gᶜ.IsHomogeneous s ↔ G.IsHomogeneous s := by
  simp only [IsHomogeneous, isClique_compl, isIndepSet_compl, or_comm]

/-- A finite graph is `C`-Ramsey if every homogeneous vertex set has at most
`C * log (Fintype.card V)` vertices. The logarithm is natural. -/
def IsCRamsey [Fintype V] (G : SimpleGraph V) (C : ℝ) : Prop :=
  ∀ s : Finset V, G.IsHomogeneous s →
    (s.card : ℝ) ≤ C * Real.log (Fintype.card V)

variable [Fintype V] {C : ℝ}

@[simp] theorem isCRamsey_compl : Gᶜ.IsCRamsey C ↔ G.IsCRamsey C := by
  simp only [IsCRamsey, isHomogeneous_compl]

/-- The Ramsey bound is equivalent to bounds on the clique and independence numbers. -/
theorem isCRamsey_iff : G.IsCRamsey C ↔
    (G.cliqueNum : ℝ) ≤ C * Real.log (Fintype.card V) ∧
      (G.indepNum : ℝ) ≤ C * Real.log (Fintype.card V) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    obtain ⟨t, ht⟩ := G.exists_isNIndepSet_indepNum
    constructor
    · simpa only [hs.card_eq] using h s (Or.inl hs.isClique)
    · simpa only [ht.card_eq] using h t (Or.inr ht.isIndepSet)
  · rintro ⟨hc, hi⟩ s (hs | hs)
    · exact (Nat.cast_le.mpr hs.card_le_cliqueNum).trans hc
    · exact (Nat.cast_le.mpr hs.card_le_indepNum).trans hi

end SimpleGraph
