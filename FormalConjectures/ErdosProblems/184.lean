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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 184

*References:*
- [erdosproblems.com/184](https://www.erdosproblems.com/184)
- [BM22] Bucić, M. and Montgomery, R., Towards the Erdős-Gallai Cycle Decomposition Conjecture.
  arXiv:2211.07689 (2022).
- [CFS14] Conlon, David and Fox, Jacob and Sudakov, Benny, Cycle packing. Random Structures
  Algorithms (2014), 608-626.
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open Filter SimpleGraph Classical

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

/-- D is a decomposition of G into subgraphs. -/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

/--
Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.
-/
@[category research open, AMS 5]
theorem erdos_184 :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

/--
Erdős and Gallai proved that $O(n \log n)$ many cycles and edges suffices.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.n_log_n :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

/--
The graph $K_{3,n-3}$ shows that at least $(1+c)n$ many cycles and edges are required, for some
constant $c>0$.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop,
      let G : SimpleGraph (Fin n) := fromRel (fun (i j : Fin n) => (i : ℕ) < 3 ∧ 3 ≤ (j : ℕ));
      ∀ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) →
        IsDecomposition G D →
        (1 + c) * (n : ℝ) ≤ (D.card : ℝ) := by
  sorry

/--
In [Er71] Erdős suggests that only $n-1$ many cycles and edges are required if we do not
require them to be edge-disjoint.
-/
@[category research open, AMS 5]
theorem erdos_184.variants.covering :
    answer(sorry) ↔
      ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        (⋃ H ∈ D, H.edgeSet) = G.edgeSet ∧
        (D.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
  sorry

/--
The best bound available is due to Bucić and Montgomery [BM22], who prove that $O(n\log^* n)$ many
cycles and edges suffice, where $\log^*$ is the iterated logarithm function.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.bucic_montgomery :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ) * (Real.iteratedLog (n : ℝ) : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

/--
Conlon, Fox, and Sudakov [CFS14] proved that $O_\epsilon(n)$ cycles and edges suffice if $G$ has
minimum degree at least $\epsilon n$, for any $\epsilon>0$.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.conlon_fox_sudakov :
    ∀ ε > 0, ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (G.minDegree : ℝ) ≥ ε * (Fintype.card V : ℝ) →
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

end Erdos184
