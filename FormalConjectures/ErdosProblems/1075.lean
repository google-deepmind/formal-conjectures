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
# Erdős Problem 1075

For every $r \geq 3$, there exists $c_r > r^{-r}$ such that for any $\varepsilon > 0$, if $n$ is
sufficiently large, any $r$-uniform hypergraph on $n$ vertices with at least
$(1+\varepsilon)(n/r)^r$ edges contains a subgraph on $m$ vertices with at least $c_r m^r$ edges,
where $m \to \infty$ as $n \to \infty$.

*References:*
- [Er74c] Erdős, P., _Extremal problems on graphs and hypergraphs_. (1974), p.80.
- [Er64f] Erdős, P., _On extremal problems of graphs and generalized graphs_. Israel J. Math. **2**
  (1964), 183-190.
- [erdosproblems.com/1075](https://www.erdosproblems.com/1075)
-/

open Finset

namespace Erdos1075

/-- An $r$-uniform hypergraph on $n$ vertices. -/
structure UniformHypergraph (n r : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- The subhypergraph of $H$ induced by a vertex set $S$: all edges entirely within $S$.
Returns the edge set (as a `Finset`) rather than a `UniformHypergraph`. -/
def UniformHypergraph.inducedSubgraph {n r : ℕ}
    (H : UniformHypergraph n r) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.edges.filter (fun e => e ⊆ S)

/--
Erdős Problem 1075:

For every $r \geq 3$, there exists $c_r > r^{-r}$ such that for any $\varepsilon > 0$,
for any target size $M$, for all sufficiently large $n$, any $r$-uniform hypergraph
on $n$ vertices with at least $(1+\varepsilon)(n/r)^r$ edges contains a vertex subset $S$
with $|S| \geq M$ and at least $c_r \cdot |S|^r$ edges within $S$.

The condition "$m \to \infty$ as $n \to \infty$" is captured by the universal quantifier over $M$:
for every $M$, eventually (for large $n$) we can find a subgraph on $\geq M$ vertices.
-/
@[category research open, AMS 5]
theorem erdos_1075 (r : ℕ) (hr : r ≥ 3) :
    ∃ c_r : ℝ, c_r > 1 / (r : ℝ) ^ r ∧
    ∀ ε : ℝ, ε > 0 →
    ∀ M : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : UniformHypergraph n r,
    (H.edges.card : ℝ) ≥ (1 + ε) * ((n : ℝ) / r) ^ r →
    ∃ S : Finset (Fin n),
      S.card ≥ M ∧
      ((H.inducedSubgraph S).card : ℝ) ≥ c_r * (S.card : ℝ) ^ r := by
  sorry

/--
Erdős [Er64f] proved that the conclusion of Problem 1075 holds with the weaker density constant
$c_r = r^{-r}$ when the edge threshold is strengthened to $\varepsilon n^r$ (instead of
$(1+\varepsilon)(n/r)^r$). This is a solved, weaker variant of the main conjecture.
-/
@[category research solved, AMS 5]
theorem erdos_1075_erdos_1964 (r : ℕ) (hr : r ≥ 3) :
    ∀ ε : ℝ, ε > 0 →
    ∀ M : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : UniformHypergraph n r,
    (H.edges.card : ℝ) ≥ ε * (n : ℝ) ^ r →
    ∃ S : Finset (Fin n),
      S.card ≥ M ∧
      ((H.inducedSubgraph S).card : ℝ) ≥ (1 / (r : ℝ) ^ r) * (S.card : ℝ) ^ r := by
  sorry

end Erdos1075
