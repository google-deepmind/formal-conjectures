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

import FormalConjecturesUtil

/-!
# Erdős Problem 834

*References:*
- [erdosproblems.com/834](https://www.erdosproblems.com/834)
- [Li25] R. Li, On an Erdős-Lovász problem: $3$-critical $3$-graphs of minimum degree $7$.
arXiv:2512.24850 (2025).
-/

namespace Erdos834

open Filter Asymptotics

/--
Does there exist a $3$-critical $3$-uniform hypergraph in which every vertex has degree
$\geq 7$, where criticality means that the transversal number is $3$ and deleting any edge
reduces it to $2$?

In the first formulation, the transversal notion of criticality, Li [Li25] proves that a
$3$-critical $3$-uniform hypergraph must have a vertex of degree $\leq 6$.
-/
@[category research solved, AMS 5]
theorem erdos_834.parts.i :
    answer(False) ↔ ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
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
@[category research solved, AMS 5]
theorem erdos_834.parts.ii :
    answer(True) ↔ ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform 3 ∧ H.HasHypergraphChromaticNumber 3 ∧
      (∀ e ∈ H, (H.erase e).HypergraphColorable 2) ∧
      (∀ v : Fin n, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable 2) ∧
      ∀ v : Fin n, 7 ≤ H.hypergraphDegree v := by
  sorry

end Erdos834
