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
module

public import Mathlib
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Multiset.Interval

@[expose] public section

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Abbreviation for the average independence number of the neighborhoods.
-/
noncomputable abbrev l (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- The same quantity under a different name, used in some conjectures.
-/
noncomputable abbrev l_avg (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- Independent domination number of `G`. -/
noncomputable def gi (G : SimpleGraph α) : ℕ := G.indepDominationNumber

/-- `temp_v G v = deg(v)/(n(G) - deg(v))`. -/
noncomputable def temp_v (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℝ :=
  let n := Fintype.card α
  let deg := G.degree v
  if n = deg then 0 else (deg : ℝ) / ((n : ℝ) - (deg : ℝ))

/-- Maximum of `temp_v` over all vertices. -/
noncomputable def MaxTemp (G : SimpleGraph α) [DecidableRel G.Adj] [Fintype α] [Nonempty α] : ℝ :=
  let temps := Finset.univ.image (temp_v G)
  temps.max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e

/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)

/-- Size of a largest induced forest of `G` expressed as a real number. -/
noncomputable def S (G : SimpleGraph α) : ℝ :=
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := degrees.sort (· ≤ ·)
    ↑((sorted_degrees[card - 2]?).getD 0)

/-- Local eccentricity of a vertex. -/
noncomputable def local_eccentricity (G : SimpleGraph α) (v : α) : ENat :=
  sSup (Set.range (G.edist v))

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)



/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

/-- The same quantity as a real number. -/
noncomputable def p (G : SimpleGraph α) : ℝ := (pathCoverNumber G : ℝ)

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

/-- The annihilation number of a graph. This is the largest number of degrees that can be added
together without going over the total number of edges of that graph. -/
def annihilationNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Calculate the limit: The number of edges (Sum of degrees / 2)
  letI limit := G.edgeFinset.card

  -- The set of all multisets of degrees that sum to less than or equal to `limit`
  Finset.Iic (degreeMultiset G)
    |>.filter (fun S ↦ Multiset.sum S ≤ limit)
    |>.sup Multiset.card

/--
Computes the annihilation number of a graph G.

It calculates the degree sequence, sorts it ascendingly, and finds the largest prefix length 'k'
(where `0 ≤ k ≤ |V(G)|`) such that the sum of the prefix is less than or equal to the sum of the corresponding suffix.
-/
noncomputable def annihilationNumber' (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- 1. Get the degree sequence sorted in ascending order.
  -- G.degree_list returns the list of degrees.
  letI degrees := (Finset.univ.image fun v => G.degree v).sort (· ≤ ·)

  -- 2. Define the condition for the annihilation number.
  -- k represents the number of smallest degrees considered (the length of the prefix).
  letI condition (k : ℕ) : Bool := (degrees.take k).sum ≤ (degrees.drop k).sum

  -- 3. Find the maximum k in {0, ..., n} satisfying the condition.
  -- List.range (n + 1) generates the list [0, 1, ..., n].
  letI candidates := (List.range (Fintype.card α + 1)).filter condition

  -- 4. Return the maximum candidate.
  -- The list of candidates is guaranteed to be non-empty because k=0 always satisfies
  -- the condition (0 ≤ sum of all degrees).
  candidates.getLast!

set_option linter.unusedSectionVars false in
-- TODO(Paul-Lez): debug the issue with the unused variable linter...
proof_wanted annihilationNumberEq (G : SimpleGraph α) [DecidableRel G.Adj] :
    annihilationNumber G = annihilationNumber' G

/--
Given a simple graph `G` with adjacency matrix `A`, this is the number `n₀ + min n₊ n₋` where:
- `n₀` is the multiplicity of zero as an eigenvalue of `A`
- `n₊` is the number of positive eigenvalues of `A` (counting multiplicities)
- `n₋` is the number of negative eigenvalues of `A` (counting multiplicities)
-/
noncomputable def cvetkovic (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI A : Matrix α α ℝ := G.adjMatrix ℝ
  letI spectrum : Multiset ℝ := (Matrix.charpoly A).roots
  letI positive_count : ℕ := spectrum.countP (fun x => 0 < x)
  letI negative_count : ℕ := spectrum.countP (fun x => 0 > x)
  letI zero_count : ℕ := spectrum.countP (fun x => 0 = x)
  zero_count + min positive_count negative_count

-- ================================================================
-- Equivalence between noncomputable and computable graph invariants
-- ================================================================

theorem indep_num_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.indepNum = computable_indep_num G := by
  unfold SimpleGraph.indepNum SimpleGraph.computable_indep_num
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      simp [SimpleGraph.IsIndepSet]
    · intro n hn
      obtain ⟨s, hs⟩ := hn
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


theorem dom_num_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    dominationNumber G = computable_dom_num G := by
  unfold SimpleGraph.dominationNumber SimpleGraph.computable_dom_num
  apply le_antisymm
  · apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    simp only [Set.mem_setOf_eq]
    obtain ⟨D, hD_mem, hD_card⟩ := Finset.exists_mem_eq_inf' _ Finset.card
    exact ⟨D, hD_card ▸ ⟨(Finset.mem_filter.mp hD_mem).2, rfl⟩⟩
  · apply le_csInf
    · exact ⟨Fintype.card α, Finset.univ,
        ⟨fun v => Or.inl (Finset.mem_univ v), Finset.card_univ⟩⟩
    · intro b hb
      obtain ⟨D, hD⟩ := hb
      rw [← hD.card_eq]
      exact Finset.inf'_le _
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          hD.isDominating⟩)

end SimpleGraph
