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
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace SimpleGraph
open Classical Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The maximum cardinality among all independent sets `s`
    that maximize the quantity `|s| - |N(s)|`, where `N(s)`
    is the neighborhood of the set `s`. -/
noncomputable def aprime (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  letI indep_sets : Finset (Finset α) := univ.powerset.filter (fun s => G.IsIndepSet (s : Set α))
  letI diff (s : Finset α) : ℤ := (s.card : ℤ) - (⋃ v ∈ (s : Set α), G.neighborSet v).toFinset.card
  letI max_diff := (indep_sets.image diff).max
  letI critical_sets := indep_sets.filter (fun s ↦ diff s = max_diff.getD 0)
  letI max_card := (critical_sets.image Finset.card).max
  (max_card.getD 0 : ℝ)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Average of `indepNeighbors` over all vertices. -/
noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

/-- Abbreviation for the average independence number of the neighborhoods.
-/
noncomputable abbrev l (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- The same quantity under a different name, used in some conjectures.
-/
noncomputable abbrev l_avg (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- Computable independence number via powerset enumeration. -/
def computable_indep_num (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter (fun s : Finset α =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v)).sup Finset.card

/-- Equivalence between computable and noncomputable independence number. -/
theorem indep_num_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.indepNum = computable_indep_num G := by
  unfold SimpleGraph.indepNum SimpleGraph.computable_indep_num
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      simp [SimpleGraph.IsIndepSet]
    · rintro n ⟨s, hs⟩
      calc n = s.card := hs.card_eq.symm
        _ ≤ _ := Finset.le_sup ?_
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, fun u hu v hv huv =>
        hs.isIndepSet (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv⟩
  · apply Finset.sup_le
    intro s hs
    apply le_csSup
    · exact ⟨Fintype.card α, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ⟩
    · simp only [Set.mem_setOf_eq]
      exact ⟨s, ⟨fun x hx y hy hne =>
        (Finset.mem_filter.mp hs).2 x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne,
        rfl⟩⟩

/-- Maximum local independence number over all vertices.
    For each vertex, we compute the independence number of the subgraph
    induced by its neighbors, and take the maximum over all vertices. -/
noncomputable def maxLocalIndependence (G : SimpleGraph α) : ℕ :=
  let locals := Finset.univ.image (fun v => (G.induce (G.neighborSet v)).indepNum)
  (locals.max).getD 0

/-- Minimum local independence number over all vertices.
    For each vertex, we compute the independence number of the subgraph
    induced by its neighbors, and take the minimum over all vertices. -/
noncomputable def minLocalIndependence (G : SimpleGraph α) : ℕ :=
  let locals := Finset.univ.image (fun v => (G.induce (G.neighborSet v)).indepNum)
  (locals.min).getD 0


end SimpleGraph
