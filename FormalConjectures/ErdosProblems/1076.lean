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
# Erdős Problem 1076

*Reference:* [erdosproblems.com/1076](https://www.erdosproblems.com/1076)

Let $k \geq 5$ and let $\mathcal{F}_k$ be the family of all 3-uniform hypergraphs with $k$
vertices and $k - 2$ edges. Is it true that $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$?

A question of Brown, Erdős, and Sós [BES73] who proved this is true for $k = 4$,
and that for all $k \geq 4$, $\mathrm{ex}_3(n, \mathcal{F}_k) \asymp_k n^2$.
Erdős [Er74c] presents the conjecture with a supporting theorem.

The asymptotic version was proved independently by Bohman and Warnke [BoWa19]
and Glock, Kühn, Lo, and Osthus [GKLO20].

This is related to Problem #207, which is an essentially stronger version.

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., *Some extremal problems on r-graphs* (1973), 53–63.

[Er74c] Erdős, P., *Extremal problems on graphs and hypergraphs*. (1974), 75–84.

[BoWa19] Bohman, T. and Warnke, L., *Large girth approximate Steiner triple systems*.
J. London Math. Soc. (2) (2019), 895–913.

[GKLO20] Glock, S., Kühn, D., Lo, A., and Osthus, D.,
*On a conjecture of Erdős on locally sparse Steiner triple systems*.
Combinatorica (2020), 363–403.
-/

open Finset

namespace Erdos1076

/-- A 3-uniform hypergraph on $n$ vertices. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph $G$ on $k$ vertices is a subhypergraph of $H$ on $n$ vertices
if there is an injection from $\mathrm{Fin}(k)$ to $\mathrm{Fin}(n)$ mapping every edge of
$G$ to an edge of $H$. -/
def IsSubhypergraph {k n : ℕ} (G : Hypergraph3 k) (H : Hypergraph3 n) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    ∀ e ∈ G.edges, e.image f ∈ H.edges

/-- $\mathcal{F}_k$: the family of all 3-uniform hypergraphs with $k$ vertices and exactly
$k - 2$ edges. -/
def familyF (k : ℕ) : Set (Hypergraph3 k) :=
  {G | G.edges.card = k - 2}

/-- $H$ is $\mathcal{F}_k$-free if it contains no subhypergraph from $\mathcal{F}_k$. -/
def IsFkFree {n : ℕ} (k : ℕ) (H : Hypergraph3 n) : Prop :=
  ∀ G : Hypergraph3 k, G ∈ familyF k → ¬IsSubhypergraph G H

/-- The extremal number $\mathrm{ex}_3(n, \mathcal{F}_k)$: the maximum number of edges in an
$\mathcal{F}_k$-free 3-uniform hypergraph on $n$ vertices. -/
noncomputable def ex3 (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Hypergraph3 n, IsFkFree k H ∧ H.edges.card = m}

/--
Erdős Problem 1076 [BES73]:

For all $k \geq 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$.

Formalized as: for every $\varepsilon > 0$, for sufficiently large $n$,
$(1 - \varepsilon) \cdot n^2 / 6 \leq \mathrm{ex}_3(n, \mathcal{F}_k)
\leq (1 + \varepsilon) \cdot n^2 / 6$.
-/
@[category research solved, AMS 5]
theorem erdos_1076 : answer(True) ↔
    ∀ k : ℕ, k ≥ 5 →
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) ^ 2 / 6) ≤ (ex3 n k : ℝ) ∧
      (ex3 n k : ℝ) ≤ (1 + ε) * ((n : ℝ) ^ 2 / 6) := by
  sorry

end Erdos1076
