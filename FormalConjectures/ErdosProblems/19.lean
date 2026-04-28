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
-/

universe u

open SimpleGraph

namespace Erdos19

variable {V : Type*}

/--
A graph $G$ is an edge-disjoint union of $n$ copies of $K_n$ if there exists a family of $n$
cliques, each of size $n$, such that any two cliques share at most one vertex.

The condition that two cliques share at most one vertex implies edge-disjointness:
if they shared two vertices, they would share the edge between them.
-/
def IsEdgeDisjointCompleteUnion (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (cliques : Fin n → Set V),
    (∀ i, (cliques i).ncard = n) ∧
    (∀ i, G.IsClique (cliques i)) ∧
    (∀ i j, i ≠ j → (cliques i ∩ cliques j).ncard ≤ 1) ∧
    (∀ v w, G.Adj v w → ∃ i, v ∈ cliques i ∧ w ∈ cliques i)

/--
The Erdős-Faber-Lovász Conjecture: if $G$ is an edge-disjoint union of $n$ copies of $K_n$,
then $\chi(G) = n$.

This was proved for all sufficiently large $n$ by Kang, Kelly, Kühn, Methuku, and Osthus (2021).
The full conjecture is still open, up to a finite check.
-/
@[category research open, AMS 5]
theorem erdos_19 :
    answer(sorry) ↔
      ∀ n > 0, ∀ (V : Type u) (G : SimpleGraph V), IsEdgeDisjointCompleteUnion G n →
        G.chromaticNumber = n := by
  sorry

/--
The asymptotic version: for all sufficiently large $n$, if $G$ is an edge-disjoint union of
$n$ copies of $K_n$, then $\chi(G) = n$.

This is the form proved by Kang, Kelly, Kühn, Methuku, and Osthus (2021).
-/
@[category research solved, AMS 5]
theorem erdos_19.asymptotic :
    ∀ᶠ n in Filter.atTop, ∀ (V : Type u) (G : SimpleGraph V),
      IsEdgeDisjointCompleteUnion G n → G.chromaticNumber = n := by
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
  intro V G ⟨cliques, hcard, hclique, _, _⟩
  set i₀ : Fin n := ⟨0, hn⟩
  have hfin : (cliques i₀).Finite := Set.finite_of_ncard_ne_zero (by rw [hcard i₀]; omega)
  have hclique₀ : G.IsClique (↑hfin.toFinset) := by
    rw [Set.Finite.coe_toFinset]
    exact hclique i₀
  convert hclique₀.card_le_chromaticNumber using 1
  norm_cast
  exact (hcard i₀).symm.trans (Set.ncard_eq_toFinset_card _ hfin)

end Erdos19
