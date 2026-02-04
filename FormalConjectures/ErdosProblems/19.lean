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
# Erdős Problem 19

*Reference:* [erdosproblems.com/19](https://www.erdosproblems.com/19)

The Erdős-Faber-Lovász Conjecture: if $G$ is an edge-disjoint union of $n$ copies of $K_n$,
then $\chi(G) = n$.

This was proved asymptotically by Kang, Kelly, Kühn, Methuku, and Osthus (2021).
-/

universe u

open SimpleGraph

namespace Erdos19

variable {V : Type*}

/--
A graph $G$ is an edge-disjoint union of $n$ copies of $K_n$ if there exists a family of $n$
cliques, each of size $n$, such that any two cliques share at most one vertex.
-/
def IsEdgeDisjointCompleteUnion (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (cliques : Fin n → Set V),
    -- Each clique has exactly n vertices
    (∀ i, (cliques i).ncard = n) ∧
    -- Each clique induces a complete graph
    (∀ i, ∀ v ∈ cliques i, ∀ w ∈ cliques i, v ≠ w → G.Adj v w) ∧
    -- Two distinct cliques share at most one vertex (edge-disjoint)
    (∀ i j, i ≠ j → (cliques i ∩ cliques j).ncard ≤ 1) ∧
    -- The graph G is exactly the union of all clique edges
    (∀ v w, G.Adj v w ↔ ∃ i, v ∈ cliques i ∧ w ∈ cliques i ∧ v ≠ w)

/--
The Erdős-Faber-Lovász Conjecture: if $G$ is an edge-disjoint union of $n$ copies of $K_n$,
then $\chi(G) = n$.
-/
@[category research solved, AMS 5]
theorem erdos_19 (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type u) (G : SimpleGraph V), IsEdgeDisjointCompleteUnion G n →
      G.chromaticNumber = n := by
  sorry

/--
The weaker statement: $\chi(G) \leq n$ for edge-disjoint union of $n$ copies of $K_n$.
-/
@[category research solved, AMS 5]
theorem erdos_19.upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type u) (G : SimpleGraph V), IsEdgeDisjointCompleteUnion G n →
      G.chromaticNumber ≤ n := by
  sorry

/--
The lower bound: $\chi(G) \geq n$ for edge-disjoint union of $n$ copies of $K_n$.
This follows from the fact that each $K_n$ requires $n$ colors.
-/
@[category graduate, AMS 5]
theorem erdos_19.lower_bound (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type u) (G : SimpleGraph V), IsEdgeDisjointCompleteUnion G n →
      n ≤ G.chromaticNumber := by
  sorry

end Erdos19
