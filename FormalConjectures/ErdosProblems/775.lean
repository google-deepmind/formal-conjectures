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
# Erdős Problem 775

*Reference:* [erdosproblems.com/775](https://www.erdosproblems.com/775)

Is there a 3-uniform hypergraph on $n$ vertices which contains at least
$n - O(1)$ different sizes of cliques (maximal complete subgraphs)?

DISPROVED: The answer is no, as proved by Gao [Ga25]. More generally, for any
$k \geq 3$, every $k$-uniform hypergraph on $n$ vertices contains at most
$n - f_k(n)$ different sizes of cliques, where $f_k(n) \to \infty$ as $n \to \infty$.

See also [927].

[Gu83] Guy, R.K., _Unsolved Problems in Number Theory_, 1983.
[Sp71] Spencer, J., _On cliques in graphs_. Israel J. Math. (1971), 419–421.
[MoMo65] Moon, J.W., Moser, L., _On cliques in graphs_. Israel J. Math. (1965), 23–28.
[Ga25] Gao, J., _On cliques in hypergraphs_. arXiv:2510.14804 (2025).
-/

namespace Erdos775

/-- A subset $S$ of vertices is complete in a $k$-uniform hypergraph $H$ if every
$k$-element subset of $S$ belongs to $H$. -/
def IsCompleteInHypergraph {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), T ⊆ S → T.card = k → T ∈ H

/-- A clique in a $k$-uniform hypergraph is a maximal complete subhypergraph:
$S$ is complete and no strict superset of $S$ is complete. -/
def IsHypergraphClique {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ)
    (S : Finset (Fin n)) : Prop :=
  IsCompleteInHypergraph H k S ∧
  ∀ T : Finset (Fin n), S ⊂ T → ¬IsCompleteInHypergraph H k T

/-- The set of distinct clique sizes in a $k$-uniform hypergraph. -/
def cliqueSizeSet {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ S : Finset (Fin n), IsHypergraphClique H k S ∧ S.card = m}

/--
Erdős Problem 775 (DISPROVED by Gao [Ga25]):

There is no 3-uniform hypergraph on $n$ vertices which contains at least $n - O(1)$
different sizes of cliques. That is, there is no constant $C$ such that for all $n$,
there exists a 3-uniform hypergraph on $n$ vertices with at least $n - C$ distinct
clique sizes.

More generally, for any $k \geq 3$, the number of distinct clique sizes in any
$k$-uniform hypergraph on $n$ vertices is at most $n - f_k(n)$ where $f_k(n) \to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_775 : answer(False) ↔
    (∃ C : ℕ, ∀ n : ℕ, ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (cliqueSizeSet H 3).ncard ≥ n - C) := by
  sorry

/--
General version of Erdős Problem 775 (Gao [Ga25]):
For any $k \geq 3$, the number of distinct clique sizes in any $k$-uniform
hypergraph on $n$ vertices is at most $n - f_k(n)$ where $f_k(n) \to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_775_general_k :
    ∀ k : ℕ, k ≥ 3 → ∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)),
        (∀ e ∈ H, e.card = k) →
        (cliqueSizeSet H k).ncard + f n ≤ n := by
  sorry

end Erdos775
