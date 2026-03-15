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
# Erdős Problem 585

*Reference:* [erdosproblems.com/585](https://www.erdosproblems.com/585)

What is the maximum number of edges that a graph on $n$ vertices can have if it
does not contain two edge-disjoint cycles with the same vertex set?

A problem of Erdős [Er76b].

Pyber, Rödl, and Szemerédi [PRS95] constructed such a graph with
$\gg n \log \log n$ edges (lower bound).

Chakraborti, Janzer, Methuku, and Montgomery [CJMM24] showed that such a
graph can have at most $n \cdot (\log n)^{O(1)}$ many edges (upper bound).

[Er76b] Erdős, P., _Problems in combinatorial and graph theory_ (1976).

[PRS95] Pyber, L., Rödl, V., Szemerédi, E., _Dense graphs without
3-regular subgraphs_. Journal of Combinatorial Theory, Series B (1995), 41-54.

[CJMM24] Chakraborti, D., Janzer, O., Methuku, A., Montgomery, R.,
_Edge-disjoint cycles with the same vertex set_. arXiv:2404.07190 (2024).
-/

open SimpleGraph Classical

namespace Erdos585

/-- A graph has no two edge-disjoint cycles with the same vertex set. -/
def NoTwoEdgeDisjointCyclesSameVertexSet {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ¬∃ (u v : Fin n) (c₁ : G.Walk u u) (c₂ : G.Walk v v),
    c₁.IsCycle ∧ c₂.IsCycle ∧
    c₁.support.toFinset = c₂.support.toFinset ∧
    Disjoint c₁.edges.toFinset c₂.edges.toFinset

/-- The maximum number of edges in a graph on $n$ vertices with no two
edge-disjoint cycles sharing the same vertex set. -/
noncomputable def maxEdgesNoEdgeDisjointCycles (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    NoTwoEdgeDisjointCyclesSameVertexSet G ∧ G.edgeFinset.card = m}

/--
Erdős Problem 585:

What is the maximum number of edges that a graph on $n$ vertices can have if it
does not contain two edge-disjoint cycles with the same vertex set?
-/
@[category research open, AMS 5]
theorem erdos_585 :
    ∀ n, maxEdgesNoEdgeDisjointCycles n = answer(sorry) := by
  sorry

/--
Erdős Problem 585, Lower Bound [PRS95]:

There exists a constant $c > 0$ such that for all sufficiently large $n$,
the maximum number of edges in an $n$-vertex graph with no two edge-disjoint
cycles on the same vertex set is at least $c \cdot n \cdot \log(\log(n))$.
-/
@[category research solved, AMS 5]
theorem erdos_585.variants.lower_bound :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (maxEdgesNoEdgeDisjointCycles n : ℝ) := by
  sorry

/--
Erdős Problem 585, Upper Bound [CJMM24]:

There exists a constant $C > 0$ such that for all sufficiently large $n$,
the maximum number of edges in an $n$-vertex graph with no two edge-disjoint
cycles on the same vertex set is at most $n \cdot (\log n)^C$.
-/
@[category research solved, AMS 5]
theorem erdos_585.variants.upper_bound :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (maxEdgesNoEdgeDisjointCycles n : ℝ) ≤
        (n : ℝ) * (Real.log (n : ℝ)) ^ C := by
  sorry

/--
Erdős Problem 585, k-wise generalization [CJMM24]:

There exist constants $C > 0$ (universal) such that for any $k \geq 2$, there exists a constant
$c_k > 0$ such that every graph on $n$ vertices with at least $c_k \cdot n \cdot (\log n)^C$ edges
contains $k$ pairwise edge-disjoint cycles sharing the same vertex set.
-/
@[category research solved, AMS 5]
theorem erdos_585.variants.k_wise_generalization :
    ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 2 ≤ k →
    ∃ c_k : ℝ, 0 < c_k ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      c_k * (n : ℝ) * (Real.log (n : ℝ)) ^ C ≤ (G.edgeFinset.card : ℝ) →
      ∃ (u : Fin n) (cycles : Fin k → G.Walk u u),
        (∀ i, (cycles i).IsCycle) ∧
        (∀ i j, i ≠ j → Disjoint (cycles i).edges.toFinset (cycles j).edges.toFinset) ∧
        (∀ i j, (cycles i).support.toFinset = (cycles j).support.toFinset) := by
  sorry

end Erdos585
