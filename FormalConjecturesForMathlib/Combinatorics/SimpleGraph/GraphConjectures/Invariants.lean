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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Multiset.Interval

@[expose] public section

noncomputable def Matrix.IsHermitian.maxEigenvalue {𝕜 : Type*} [Field 𝕜] [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℝ :=
  iSup hA.eigenvalues

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

/-- The largest integer less than or equal to `x`. -/
noncomputable def FLOOR (x : ℝ) : ℝ := ⌊x⌋

/-- Eccentricity of a vertex. -/
noncomputable def eccentricity (G : SimpleGraph α) (v : α) : ℕ∞ :=
  sSup (Set.range (G.edist v))

/-- The minimum eccentricity among all vertices. -/
noncomputable def minEccentricity (G : SimpleGraph α) : ℕ∞ :=
  sInf (Set.range (eccentricity G))

/-- The set of vertices of minimum eccentricity. -/
noncomputable def graphCenter (G : SimpleGraph α) : Set α :=
  {v : α | eccentricity G v = minEccentricity G}

/-- The maximum eccentricity among all vertices. -/
noncomputable def maxEccentricity (G : SimpleGraph α) : ℕ∞ :=
  sSup (Set.range (eccentricity G))

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | eccentricity G v = maxEccentricity G}

/-- The average eccentricity of a graph `G`: the mean of `eccentricity G v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccentricity v).toNat) / (Fintype.card α : ℝ)

/-- Distance from a vertex to a finite set. -/
noncomputable def distToSet (G : SimpleGraph α) (v : α) (S : Set α) : ℕ :=
  if h : S.toFinset.Nonempty then
    (S.toFinset.image (fun s => G.dist v s)).min' (Finset.Nonempty.image h _)
  else 0

/-- Average distance of `G`. -/
noncomputable def averageDistance (G : SimpleGraph α) : ℝ :=
  if Fintype.card α > 1 then
    (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (G.dist u v : ℝ)) /
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))
  else
    0

/-- The floor of the average distance of `G`. -/
noncomputable def path (G : SimpleGraph α) : ℕ :=
  if G.Connected then
    Nat.floor (averageDistance G)
  else
    0

/-- Auxiliary quantity `ecc` used in conjecture 34. -/
noncomputable def ecc (G : SimpleGraph α) (S : Set α) : ℕ :=
  let s_comp := Finset.univ.filter (fun v => v ∉ S)
  if h : s_comp.Nonempty then
    (s_comp.image (fun v => distToSet G v S)).max' (Finset.Nonempty.image h _)
  else 0

/-- Average distance from all vertices to a given set. -/
noncomputable def distavg (G : SimpleGraph α) (S : Set α) : ℝ :=
  if Fintype.card α > 0 then
    (∑ v ∈ Finset.univ, (distToSet G v S : ℝ)) / (Fintype.card α : ℝ)
  else
    0

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

/-- The Wiener index of `G`, which is the sum of distances between all
pairs of vertices. -/
noncomputable def wienerIndex (G : SimpleGraph α) : ℕ :=
  ∑ uv : Sym2 α, uv.lift ⟨fun u v ↦ G.dist u v, by simp [dist_comm]⟩

/-- Auxiliary function for Szeged index: counts vertices closer to u than v. -/
noncomputable def szeged_aux (G : SimpleGraph α) (u v : α) : ℕ :=
  (Finset.univ.filter (fun w => G.edist w u < G.edist w v)).card

/-- The Szeged index of `G`.

This is define as the sum `∑_{uv ∈ E(G)} n_u(u,v) * n_v(u,v)` where
`n_u(uv)` is the number of vertices closer to `u` than `v`.
-/
noncomputable def szegedIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => szeged_aux G u v * szeged_aux G v u, by simp [mul_comm]⟩

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

/-!
## Residue
The residue of a graph is the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
-/

/--
Helper function: Performs one step of the Havel-Hakimi reduction on a degree sequence.
Assumes the input list `s` is sorted descending.
Removes the first element `d`, decrements the next `d` elements by 1, and re-sorts the list descending.

Note: when `s` is the list of vertices arising from a simple graph, if the first index is `s` then
the degree list always has length at least `s+1` so this makes sense.
-/
def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    -- Split the rest into the part to decrement (first d elements) and the remaining part.
    let (to_decrement, remaining) := rest.splitAt d
    -- Decrement the elements
    let decremented := to_decrement.map (· - 1)
    -- Combine and re-sort descending.
    (decremented ++ remaining).mergeSort (· ≥ ·)

/--
Auxiliary function to calculate the residue recursively.
Applies Havel-Hakimi steps until the sequence consists only of zeros or is empty.
-/
partial def residueAux : List ℕ → ℕ
  | [] => 0        -- Empty sequence, residue is 0.
  | 0 :: s => 1 + s.length -- If the largest degree is 0 (and the list is sorted), all are 0.
  | s => residueAux (havelHakimiStep s) -- Apply one reduction step and recurse.

/--
Computes the residue of a graph G, ,i.e. the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
Starts with the descending degree sequence and applies the Havel-Hakimi process.
-/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Get the degree sequence sorted in descending order and apply `residueAux`.
  residueAux ((Finset.univ.image fun v => G.degree v).sort (· ≥ ·))

/--
Fractional alpha. This is defined as
$$
\max_x \sum_{v \in V} x_v
$$
subject to $0 \le x_v \le 1$ for all $v \in V$ and
$x_u + x_v \le 1$ whenever $(u, v)$ are connected by an edge.
-/
noncomputable def fractionalAlpha (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sSup {(∑ i, x i) | (x : α → ℝ) (_ : ∀ v, x v ∈ Set.Icc 0 1)
    (_ : ∀ u v, G.Adj u v → x u + x v ≤ 1)}

/--
Lovász Theta Function (ϑ(G))
The Lovász theta function is defined as:
ϑ(G) = min λ_max(A)
where the minimum is taken over all symmetric matrices A such that:

A_ij = 1 for all i = j (diagonal entries are 1)
A_ij = 0 for all {i,j} ∈ E (entries corresponding to edges are 0)
A is positive semidefinite

Here λ_max(A) denotes the maximum eigenvalue of A.
-/
noncomputable def lovaczThetaFunction
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, G.Adj i j → A i j = 0)}

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

private lemma mem_iterate_bfs_expand_dist_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ (G.bfs_expand)^[n] {u}) : G.dist u w ≤ n := by
  induction n generalizing w with
  | zero => simp at hw; subst hw; simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hw
    rcases hw with hw | ⟨a, ha_mem, _, hadj⟩
    · exact Nat.le_succ_of_le (ih w hw)
    · by_cases ha : a = u
      · subst ha
        exact le_trans (dist_le (.cons hadj .nil))
          (by simp [Walk.length_cons])
      · by_cases hd : G.dist u a = 0
        · rw [dist_eq_zero_iff_eq_or_not_reachable] at hd
          rcases hd with rfl | hd
          · exact absurd rfl ha
          · have : ¬G.Reachable u w := fun hr =>
              hd (hr.elim (fun p => (p.append (.cons hadj.symm .nil)).reachable))
            rw [dist_eq_zero_of_not_reachable this]; omega
        · obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero hd
          have ha_dist := ih a ha_mem
          exact le_trans (dist_le (p.append (.cons hadj .nil)))
            (by simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hp]; omega)

private lemma reachable_of_mem_iterate_bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ (G.bfs_expand)^[n] {u}) : w = u ∨ G.Reachable u w := by
  induction n generalizing w with
  | zero => simp at hw; exact Or.inl hw
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hw
    rcases hw with hw | ⟨a, ha_mem, _, hadj⟩
    · exact ih w hw
    · right
      rcases ih a ha_mem with rfl | hr
      · exact hadj.reachable
      · exact hr.elim fun p => (p.append (.cons hadj .nil)).reachable

private lemma dist_le_mem_iterate_bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hdist : G.dist u w ≤ n) (hreach : w = u ∨ G.Reachable u w) :
    w ∈ (G.bfs_expand)^[n] {u} := by
  induction n generalizing w with
  | zero =>
    rcases hreach with rfl | hr
    · exact Finset.mem_singleton_self _
    · have h0 := Nat.le_zero.mp hdist
      rw [dist_eq_zero_iff_eq_or_not_reachable] at h0
      rcases h0 with h0 | h0
      · subst h0; exact Finset.mem_singleton_self _
      · exact absurd hr h0
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
    by_cases hle : G.dist u w ≤ n
    · left; exact ih w hle hreach
    · right
      have hdist_eq : G.dist u w = n + 1 := by omega
      obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist u w ≠ 0)
      have hlen : p.length = n + 1 := by omega
      refine ⟨p.getVert n, ?_, Finset.mem_univ _, ?_⟩
      · exact ih _ (le_trans (dist_le (p.take n))
          (by rw [Walk.take_length]; omega)) (Or.inr (p.take n).reachable)
      · have := p.adj_getVert_succ (show n < p.length from by omega)
        rwa [show n + 1 = p.length from by omega, p.getVert_length] at this

theorem dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) :
    G.dist u v = computable_dist G u v := by
  unfold computable_dist
  split_ifs with h
  · subst h; simp [dist_self]
  · symm
    suffices hsuff : ∀ (fuel depth : ℕ) (reached : Finset α),
        (∀ w, w ∈ reached ↔ w ∈ (G.bfs_expand)^[depth] {u}) →
        (∀ d, d < depth → v ∉ (G.bfs_expand)^[d] {u}) →
        fuel + depth ≥ Fintype.card α + 1 →
        G.bfs_dist_aux v fuel depth reached = G.dist u v by
      exact hsuff (Fintype.card α) 1 (G.bfs_expand {u})
        (fun w => by simp)
        (fun d hd => by
          have := Nat.lt_of_lt_of_le hd (Nat.le_refl 1)
          interval_cases d; simp [Finset.mem_singleton]; exact Ne.symm h)
        (by omega)
    intro fuel
    induction fuel with
    | zero =>
      intro depth reached h_inv h_not_found h_fuel
      simp [bfs_dist_aux]
      symm; rw [dist_eq_zero_iff_eq_or_not_reachable]
      right; intro hr
      have hpos := hr.pos_dist_of_ne h
      obtain ⟨p, hp_path, hp_len⟩ := hr.exists_path_of_dist
      have : G.dist u v < depth := by
        calc G.dist u v = p.length := hp_len.symm
          _ < Fintype.card α := hp_path.length_lt
          _ < depth := by omega
      exact h_not_found (G.dist u v) this
        (dist_le_mem_iterate_bfs_expand G u v _ (le_refl _) (Or.inr hr))
    | succ fuel ih =>
      intro depth reached h_inv h_not_found h_fuel
      simp only [bfs_dist_aux]
      split_ifs with hv
      · -- v ∈ reached = iterate^depth {u}. Show depth = dist u v.
        have hle := mem_iterate_bfs_expand_dist_le G u v depth ((h_inv v).mp hv)
        -- dist u v ≥ depth: if dist < depth, v ∈ iterate^(dist u v), contradicts h_not_found
        by_contra hne
        have hlt : G.dist u v < depth := by omega
        have hreach : G.Reachable u v := by
          rcases reachable_of_mem_iterate_bfs_expand G u v depth ((h_inv v).mp hv) with rfl | hr
          · exact absurd rfl h
          · exact hr
        exact h_not_found (G.dist u v) hlt
          (dist_le_mem_iterate_bfs_expand G u v _ (le_refl _) (Or.inr hreach))
      · -- v ∉ reached. Recurse.
        have h_inv' : ∀ w, w ∈ G.bfs_expand reached ↔
            w ∈ (G.bfs_expand)^[depth + 1] {u} := by
          intro w
          have heq : G.bfs_expand reached = G.bfs_expand ((G.bfs_expand)^[depth] {u}) := by
            ext x; simp only [bfs_expand, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_filter, h_inv]
          rw [heq, Function.iterate_succ', Function.comp]
        exact ih (depth + 1) (G.bfs_expand reached) h_inv'
          (fun d hd => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
            · exact h_not_found d (by omega)
            · subst hd; rwa [h_inv] at hv)
          (by omega)

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

-- Helper: edist comparison ↔ dist comparison for adjacent endpoints
omit [Fintype α] [DecidableEq α] in
private lemma edist_lt_iff_dist_lt (G : SimpleGraph α) {u v : α} (hadj : G.Adj u v) (w : α) :
    G.edist w u < G.edist w v ↔ G.dist w u < G.dist w v := by
  by_cases hru : G.Reachable w u
  · have hrv : G.Reachable w v := hru.trans hadj.reachable
    rw [← hru.coe_dist_eq_edist, ← hrv.coe_dist_eq_edist, ENat.coe_lt_coe]
  · have hrv : ¬G.Reachable w v :=
      fun h => hru (h.trans hadj.symm.reachable)
    simp [edist_eq_top_of_not_reachable hru, edist_eq_top_of_not_reachable hrv,
          dist_eq_zero_of_not_reachable hru, dist_eq_zero_of_not_reachable hrv]

private lemma szeged_aux_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v : α} (hadj : G.Adj u v) :
    szeged_aux G u v = computable_szeged_aux G u v := by
  unfold szeged_aux computable_szeged_aux
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [edist_lt_iff_dist_lt G hadj w, dist_eq_computable, dist_eq_computable]

theorem szeged_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    szegedIndex G = computable_szeged_index G := by
  unfold szegedIndex computable_szeged_index
  apply Finset.sum_congr rfl
  intro e he
  revert he
  refine Sym2.ind (fun u v => ?_) e
  intro he
  simp only [Sym2.lift_mk]
  have hadj : G.Adj u v := by rwa [mem_edgeFinset, mem_edgeSet] at he
  congr 1
  · exact szeged_aux_eq_computable G hadj
  · exact szeged_aux_eq_computable G hadj.symm

-- Helper: ∑∑ f = 2 * ∑ Sym2 (lift f) when f symmetric with f(a,a) = 0
private lemma double_sum_eq_two_mul_sym2_sum {f : α → α → ℕ}
    (hf : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    ∑ u : α, ∑ v : α, f u v =
    2 * ∑ x : Sym2 α, Sym2.lift ⟨f, fun a b => hf a b⟩ x := by
  -- Use fiberwise decomposition over Sym2 quotient map
  have h_fiber := Fintype.sum_fiberwise
    (fun (p : α × α) => Sym2.mk p)
    (fun (p : α × α) => f p.1 p.2)
  -- h_fiber : ∑ q : Sym2 α, ∑ p : {p // Sym2.mk p = q}, f (↑p).1 (↑p).2
  --         = ∑ p : α × α, f p.1 p.2
  -- RHS = ∑ u, ∑ v, f u v (by Finset.sum_product')
  -- LHS = ∑ q, (fiber sum) = ∑ q, 2 * lift f q = 2 * ∑ q, lift f q
  -- So: ∑ u, ∑ v, f u v = 2 * ∑ q, lift f q
  rw [show (∑ u : α, ∑ v : α, f u v) = ∑ p : α × α, f p.1 p.2 from by
    rw [← Finset.univ_product_univ, Finset.sum_product']]
  rw [← h_fiber, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  -- For each q : Sym2 α, show fiber sum = 2 * lift f q
  refine Sym2.ind (fun a b => ?_) q
  simp only [Sym2.lift_mk]
  -- Need: ∑ (p : {p : α × α // Sym2.mk p = s(a, b)}), f (↑p).1 (↑p).2 = 2 * f a b
  -- Convert subtype sum to filter sum
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : α × α => Sym2.mk p = s(a, b)))
    (fun x => by simp [Finset.mem_filter]) (fun p => f p.1 p.2)]
  -- Characterize the filter: Sym2.mk (x,y) = s(a,b) ↔ (x,y) = (a,b) ∨ (x,y) = (b,a)
  have h_filter : Finset.univ.filter (fun p : α × α => Sym2.mk p = s(a, b)) =
      {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      rw [Sym2.eq] at h
      cases h with
      | refl => left; exact ⟨rfl, rfl⟩
      | swap => right; exact ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact Sym2.sound (.swap _ _)
  rw [h_filter]
  by_cases hab : a = b
  · subst hab; simp [hd]
  · rw [Finset.sum_pair (show (a, b) ≠ (b, a) by simp [hab])]
    rw [hf b a]; ring

theorem wiener_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    wienerIndex G = computable_wiener G := by
  unfold wienerIndex computable_wiener
  -- Goal: ∑ uv, Sym2.lift ⟨dist, _⟩ uv = (∑ u, ∑ v, computable_dist u v) / 2
  have hcomm : ∀ a b, computable_dist G a b = computable_dist G b a := by
    intro a b; rw [← dist_eq_computable, ← dist_eq_computable, dist_comm]
  have hdiag : ∀ a, computable_dist G a a = 0 := by
    intro a; rw [← dist_eq_computable]; simp
  -- Sum over Sym2 using dist = sum over Sym2 using computable_dist
  have h_sum : (∑ uv : Sym2 α, Sym2.lift ⟨fun u v ↦ G.dist u v,
      by intro a b; simp [dist_comm]⟩ uv) =
      ∑ uv : Sym2 α, Sym2.lift ⟨fun u v ↦ computable_dist G u v,
      fun a b => hcomm a b⟩ uv := by
    apply Finset.sum_congr rfl; intro x _
    refine Sym2.ind (fun a b => ?_) x
    simp only [Sym2.lift_mk, dist_eq_computable]
  rw [h_sum]
  have h2 := double_sum_eq_two_mul_sym2_sum hcomm hdiag
  -- h2 : ∑∑ f = 2 * ∑ Sym2 lift f
  -- goal: ∑ Sym2 lift f = ∑∑ f / 2
  rw [h2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

theorem avg_dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    averageDistance G = (computable_avg_dist G : ℝ) := by
  unfold averageDistance computable_avg_dist
  split_ifs with h
  · -- numerator equality
    have hnum : (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (G.dist u v : ℝ)) =
        ↑(∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (computable_dist G u v : ℚ)) := by
      push_cast
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      simp [dist_eq_computable]
    rw [hnum]
    push_cast
    ring
  · simp

end SimpleGraph
