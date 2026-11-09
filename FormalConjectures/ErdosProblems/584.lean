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
# Erdős Problem 584

*References:*
- [erdosproblems.com/584](https://www.erdosproblems.com/584)
- [DuEr82] Duke, Richard and Erdős, Paul, *Subgraphs in which each pair of edges lies in a
  short common cycle*. Congr. Numer. 35 (1982), 253-260.
- [DER84] Duke, Richard, Erdős, Paul, and Rödl, Vojtěch, *More results on subgraphs with many
  short cycles*. Congr. Numer. 43 (1984), 295-300.
- [FoSu08b] Fox, Jacob and Sudakov, Benny, *On a problem of Duke-Erdős-Rödl on cycle-connected
  subgraphs*. J. Combin. Theory Ser. B (2008), 1056-1062.
-/

@[expose] public section

namespace Erdos584

open Filter SimpleGraph

variable {V : Type*}

/-- Every two distinct edges lie on a common cycle of length at most six in `H`, and
edges sharing a vertex lie on a common four-cycle in `H`. -/
def IsStronglySixCycleConnected (H : SimpleGraph V) : Prop :=
  ∀ e ∈ H.edgeSet, ∀ f ∈ H.edgeSet, e ≠ f →
    (∃ C : Cycle H, e ∈ C.edges ∧ f ∈ C.edges ∧ C.length ≤ 6) ∧
    (edgesAdjacent e f →
      ∃ C : Cycle H, e ∈ C.edges ∧ f ∈ C.edges ∧ C.length = 4)

/-- Every two distinct edges lie on a common cycle of length at most eight in `H`. -/
def IsEightCycleConnected (H : SimpleGraph V) : Prop :=
  ∀ e ∈ H.edgeSet, ∀ f ∈ H.edgeSet, e ≠ f →
    ∃ C : Cycle H, e ∈ C.edges ∧ f ∈ C.edges ∧ C.length ≤ 8

open scoped Classical in
/--
Let $G$ be a graph with $n$ vertices and $\delta n^{2}$ edges. Is there a subgraph
$H_1\subseteq G$ such that $H_1$ has $\gg \delta^3n^2$ edges and every two edges in $H_1$
are contained in a cycle of length at most $6$, and furthermore if two edges share a
vertex they are on a cycle of length $4$?

The cycles are contained in $H_1$, as in [DuEr82] and [DER84].
-/
@[category research open, AMS 5]
theorem erdos_584.parts.i : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 0 < n →
      ∀ G : SimpleGraph (Fin n), (G.edgeFinset.card : ℝ) = δ * (n : ℝ) ^ 2 →
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          c * δ ^ 3 * (n : ℝ) ^ 2 ≤ (H.edgeFinset.card : ℝ) ∧
          IsStronglySixCycleConnected H := by
  sorry

open scoped Classical in
/--
Let $G$ be a graph with $n$ vertices and $\delta n^{2}$ edges. Is there a subgraph
$H_2\subseteq G$ such that $H_2$ has $\gg \delta^2n^2$ edges and every two edges in $H_2$
are contained in a cycle of length at most $8$?

The cycles are contained in $H_2$. Without a density restriction, the answer is negative:
graphs of high girth give counterexamples, as noted in [FoSu08b, Section 3].
-/
@[category research solved, AMS 5]
theorem erdos_584.parts.ii : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 0 < n →
      ∀ G : SimpleGraph (Fin n), (G.edgeFinset.card : ℝ) = δ * (n : ℝ) ^ 2 →
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          c * δ ^ 2 * (n : ℝ) ^ 2 ≤ (H.edgeFinset.card : ℝ) ∧
          IsEightCycleConnected H := by
  sorry

open scoped Classical in
/--
Duke and Erdős [DuEr82] proved the first statement if $n$ is sufficiently large
depending on $\delta$.
-/
@[category research solved, AMS 5]
theorem erdos_584.variants.duke_erdos :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), (G.edgeFinset.card : ℝ) = δ * (n : ℝ) ^ 2 →
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          c * δ ^ 3 * (n : ℝ) ^ 2 ≤ (H.edgeFinset.card : ℝ) ∧
          IsStronglySixCycleConnected H := by
  sorry

open scoped Classical in
/--
Fox and Sudakov [FoSu08b, Theorem 1.2] proved that for $0<\beta<1/5$ and sufficiently
large $n$, every graph on $n$ vertices with at least $n^{2-\beta}$ edges contains a
subgraph with at least $n^{2-2\beta}/64$ edges whose every two edges lie on a common
cycle of length at most eight in that subgraph.
-/
@[category research solved, AMS 5]
theorem erdos_584.variants.fox_sudakov :
    ∀ β : ℝ, 0 < β → β < 1 / 5 → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ (2 - β) ≤ (G.edgeFinset.card : ℝ) →
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          (n : ℝ) ^ (2 - 2 * β) / 64 ≤ (H.edgeFinset.card : ℝ) ∧
          IsEightCycleConnected H := by
  sorry

end Erdos584
