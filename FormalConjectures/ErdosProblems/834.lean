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

public import FormalConjecturesUtil

/-!
# Erdős Problem 834

*References:*
- [erdosproblems.com/834](https://www.erdosproblems.com/834)
- [Li25] R. Li, On an Erdős-Lovász problem: $3$-critical $3$-graphs of minimum degree $7$.
  arXiv:2512.24850 (2025).
-/

@[expose] public section

namespace Erdos834

open Filter Asymptotics

/-- Li's 22-edge 3-uniform hypergraph on 9 vertices, arXiv:2512.24850 eq. (5); vertices shifted to `0..8`. -/
private def liH : Finset (Finset (Fin 9)) :=
  {{0,1,2},{0,1,8},{0,2,7},{0,3,5},{0,3,7},{0,3,8},{0,4,6},{0,4,7},{0,4,8},{0,5,6},
   {1,2,5},{1,2,6},{1,3,8},{1,4,8},{1,5,6},{2,3,7},{2,4,7},{2,5,6},
   {3,5,7},{3,5,8},{4,6,7},{4,6,8}}

private instance (H : Finset (Finset (Fin 9))) (k : ℕ) : Decidable (H.HypergraphColorable k) := by
  unfold Finset.HypergraphColorable Finset.IsProperHypergraphColoring; infer_instance

private theorem liH_uniform : liH.IsUniform 3 := by
  unfold Finset.IsUniform; decide +kernel

private theorem liH_chrom : liH.HasHypergraphChromaticNumber 3 := by
  unfold Finset.HasHypergraphChromaticNumber
  refine ⟨?_, ?_⟩ <;> decide +kernel

private theorem liH_edge : ∀ e ∈ liH, (liH.erase e).HypergraphColorable 2 := by decide +kernel

private theorem liH_vertex :
    ∀ v : Fin 9, (liH.filter (fun e ↦ v ∉ e)).HypergraphColorable 2 := by decide +kernel

private theorem liH_deg : ∀ v : Fin 9, 7 ≤ liH.hypergraphDegree v := by
  unfold Finset.hypergraphDegree; decide +kernel

/--
Does there exist a $3$-critical $3$-uniform hypergraph in which every vertex has degree
$\geq 7$, where criticality means that the transversal number is $3$ and deleting any edge
reduces it to $2$?

In the first formulation, the transversal notion of criticality, Li [Li25] proves that a
$3$-critical $3$-uniform hypergraph must have a vertex of degree $\leq 6$.
-/
@[category research solved, question, AMS 5]
theorem erdos_834.parts.i :
    ¬ ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform 3 ∧ (H : Set (Finset (Fin n))).HasFiniteTransversal 3 ∧
      ¬ (H : Set (Finset (Fin n))).HasFiniteTransversal 2 ∧
      (∀ e ∈ H, (H.erase e : Set (Finset (Fin n))).HasFiniteTransversal 2) ∧
      ∀ v : Fin n, 7 ≤ H.hypergraphDegree v := by
  sorry

/--
Does there exist a $3$-critical $3$-uniform hypergraph with minimum degree at least $7$,
where criticality means that deleting any edge or vertex reduces chromatic number $3$ to $2$?

In the second formulation, the chromatic notion of criticality, Li [Li25] provides an
explicit $3$-critical $3$-uniform hypergraph on $9$ vertices with minimum degree $7$.
-/
@[category research solved, question, AMS 5]
theorem erdos_834.parts.ii :
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform 3 ∧ H.HasHypergraphChromaticNumber 3 ∧
      (∀ e ∈ H, (H.erase e).HypergraphColorable 2) ∧
      (∀ v : Fin n, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable 2) ∧
      ∀ v : Fin n, 7 ≤ H.hypergraphDegree v := by
  exact ⟨9, liH, liH_uniform, liH_chrom, liH_edge, liH_vertex, liH_deg⟩

end Erdos834
