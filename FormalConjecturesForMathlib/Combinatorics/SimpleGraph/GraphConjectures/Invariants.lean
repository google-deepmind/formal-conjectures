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

end SimpleGraph
