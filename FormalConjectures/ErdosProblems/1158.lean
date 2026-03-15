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
# Erdős Problem 1158

Erdős asks whether the extremal number for complete $t$-partite $t$-uniform hypergraphs satisfies
$\mathrm{ex}_t(n, K_t(r)) \geq n^{t - r^{1-t} - o(1)}$.

*Reference:* [erdosproblems.com/1158](https://www.erdosproblems.com/1158)

[Er64f] Erdős, P., _On extremal problems of graphs and generalized graphs_. Israel J. Math. 2
(1964), 183-190.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.65.
-/

namespace Erdos1158

/-- A $t$-uniform hypergraph on $\operatorname{Fin}(n)$: every edge has exactly $t$ vertices. -/
def IsUniformHypergraph (t : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, e.card = t

/-- A $t$-uniform hypergraph $E$ on $\operatorname{Fin}(n)$ contains a copy of the complete
$t$-partite $t$-uniform hypergraph $K_t(r)$ if there exist $t$ pairwise disjoint vertex classes,
each of size $r$, such that every transversal forms an edge of $E$. -/
def HasKtrCopy (t r : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∃ classes : Fin t → Finset (Fin n),
    (∀ i, (classes i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (classes i) (classes j)) ∧
    (∀ f : Fin t → Fin n, (∀ i, f i ∈ classes i) →
      Finset.image f Finset.univ ∈ E)

/--
**Erdős Problem 1158** [Va99, 3.65]:

Let $K_t(r)$ be the complete $t$-partite $t$-uniform hypergraph with $r$ vertices in
each class. Is it true that $\mathrm{ex}_t(n, K_t(r)) \geq n^{t - r^{1-t} - o(1)}$ for all $t, r$?

Erdős [Er64f] proved that
$n^{t - O(r^{1-t})} \leq \mathrm{ex}_t(n, K_t(r)) \ll n^{t - r^{1-t}}$.
This is only known when $t = 2$ and $2 \leq r \leq 3$. The case $t = 2$ is problem \#714.

Formally: for all $t \geq 2$, $r \geq 2$, and $\varepsilon > 0$, for sufficiently large $n$,
there exists a $t$-uniform hypergraph on $n$ vertices with no $K_t(r)$ copy and at least
$n^{t - r^{1-t} - \varepsilon}$ edges.
-/
@[category research open, AMS 5]
theorem erdos_1158 : answer(sorry) ↔
    ∀ (t r : ℕ), 2 ≤ t → 2 ≤ r →
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ E : Finset (Finset (Fin n)),
        IsUniformHypergraph t E ∧
        ¬HasKtrCopy t r E ∧
        (E.card : ℝ) ≥ (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) := by
  sorry

end Erdos1158
