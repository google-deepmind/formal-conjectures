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
# Erdős Problem 641

*References:*
- [erdosproblems.com/641](https://www.erdosproblems.com/641)
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Le Matematiche (1992), 231–240.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*.
  Discrete Math. (1997), 81–85, p.84.
- [JSS24] Janzer, Barnabás, Steiner, Raphael, and Sudakov, Benny,
  *Chromatic number and regular subgraphs*. arXiv:2410.02437 (2024).
-/

@[expose] public section

open SimpleGraph

namespace Erdos641

open scoped Classical in
/-- A finite cycle, represented by a connected $2$-regular graph. -/
def IsCycleGraph {V : Type*} [Fintype V] (C : SimpleGraph V) : Prop :=
  C.Connected ∧ C.IsRegularOfDegree 2

/-- $k$ pairwise edge-disjoint cycles on the same nonempty set of vertices.
One embedding of the union ensures that all cycles have the same ambient vertices.
The ambient graph may have additional edges between these vertices. -/
def HasCommonVertexCycles {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    ∃ C : Fin k → SimpleGraph (Fin m),
      (∀ i, IsCycleGraph (C i)) ∧
      (∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (C i) (C j)) ∧
      Nonempty (SimpleGraph.Copy (⨆ i, C i) G)

/-- The proposed chromatic thresholds for common-vertex cycles. -/
def ErdosHajnalProperty (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (f k : ℕ∞) ≤ G.chromaticNumber → HasCommonVertexCycles G k

/--
Is there some function $f$ such that for all $k\geq 1$ if a finite graph $G$ has chromatic
number $\geq f(k)$ then $G$ has $k$ edge disjoint cycles on the same set of vertices?

A problem of Erdős and Hajnal. This was resolved in the negative by Janzer, Steiner,
and Sudakov [JSS24] - in fact, this fails even at $k=2$.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos641.lean"]
theorem erdos_641 : ¬ ∃ f : ℕ → ℕ, ErdosHajnalProperty f := by
  sorry

end Erdos641
