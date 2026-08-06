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
# Erdős Problem 599

*References:*
- [erdosproblems.com/599](https://www.erdosproblems.com/599)
- [AhBe09] Aharoni, Ron and Berger, Eli, *Menger's theorem for infinite graphs*,
  *Invent. Math.* **176** (2009), 1--62.
-/

open SimpleGraph

namespace Erdos599

/--
**Erdős Problem 599** (the Erdős–Menger conjecture).

Let $G$ be a (possibly infinite) graph and let $A, B$ be disjoint independent sets of
vertices. Must there exist a family $P$ of pairwise vertex-disjoint paths from $A$ to $B$,
and a set $S$ of vertices containing exactly one vertex from each path in $P$, such that
every path from $A$ to $B$ contains at least one vertex of $S$?

For finite $G$ this is equivalent to Menger's theorem. The answer is **yes**, proved by
Aharoni and Berger [AhBe09].
-/
@[category research solved, AMS 5]
theorem erdos_599 : answer(True) ↔
    ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
      Disjoint A B → G.IsIndepSet A → G.IsIndepSet B →
      ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (p i).IsPath) ∧
        (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
        S ⊆ {v | ∃ i, v ∈ (p i).support} ∧
        (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
        (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S) := by
  sorry

/--
**Menger's theorem for infinite graphs** (Aharoni–Berger [AhBe09]).

The theorem actually proved by Aharoni and Berger holds for arbitrary vertex sets $A$
and $B$: in any (possibly infinite) graph $G$ there is a family $P$ of pairwise
vertex-disjoint $A$--$B$ paths together with an $A$--$B$ separator $S$ consisting of the
choice of exactly one vertex from each path in $P$. The disjointness and independence
hypotheses of `erdos_599` are not needed.
-/
@[category research solved, AMS 5]
theorem erdos_599.variants.aharoni_berger :
    ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
      ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (p i).IsPath) ∧
        (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
        S ⊆ {v | ∃ i, v ∈ (p i).support} ∧
        (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
        (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S) := by
  sorry

/--
Sanity check: when $A = \varnothing$ the conclusion of `erdos_599` holds trivially, with
the empty family of paths and $S = \varnothing$ (the covering condition is vacuous since
there is no path starting in $\varnothing$).
-/
@[category test, AMS 5]
theorem erdos_599.test.empty_A (V : Type) (G : SimpleGraph V) (B : Set V) :
    ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
      (∀ i, a i ∈ (∅ : Set V)) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (p i).IsPath) ∧
      (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
      S ⊆ {v | ∃ i, v ∈ (p i).support} ∧
      (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
      (∀ a' ∈ (∅ : Set V), ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath →
        ∃ v ∈ q.support, v ∈ S) := by
  refine ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim, ∅,
    fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim,
    fun v hv => hv.elim, fun i => i.elim, fun a' ha' => absurd ha' (Set.notMem_empty _)⟩

end Erdos599
