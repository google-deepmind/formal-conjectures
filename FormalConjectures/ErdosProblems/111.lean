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
# Erdős Problem 111

*References:*
- [erdosproblems.com/111](https://www.erdosproblems.com/111)
- [EHS82] Erdős, P., Hajnal, A. and Szemerédi, E., *On almost bipartite large chromatic graphs*.
  Theory and practice of combinatorics (1982), 117–123.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica 1 (1981), 25–42.
-/

@[expose] public section

open Filter
open scoped Cardinal

namespace Erdos111

variable {V : Type*}

/-- The least number of edges that must be deleted from the subgraph of `G` induced on the
finite vertex set `S` to make it bipartite. -/
noncomputable def minDelBipartite (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sInf {k : ℕ | ∃ E : Finset (Sym2 V), E.card = k ∧
    ((G.deleteEdges (E : Set (Sym2 V))).induce (S : Set V)).Colorable 2}

/-- `h G n` is $h_G(n)$: the least number such that every subgraph of `G` on `n` vertices can be
made bipartite by deleting at most `h G n` edges. It suffices to consider induced subgraphs, since
any subgraph on the vertex set `S` is a subgraph of the induced one. The value is `0` if `G` has
fewer than `n` vertices. -/
noncomputable def h (G : SimpleGraph V) (n : ℕ) : ℕ :=
  ⨆ S : {S : Finset V // S.card = n}, minDelBipartite G S.1

/--
Let $h_G(n)$ be the least number such that every subgraph of $G$ on $n$ vertices can be made
bipartite by deleting at most $h_G(n)$ edges. Is it true that $h_G(n)/n \to \infty$ for every
graph $G$ with chromatic number $\aleph_1$?
-/
@[category research open, AMS 5]
theorem erdos_111 :
    answer(sorry) ↔ ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop := by
  sorry

/-- Every graph $G$ with chromatic number $\aleph_1$ satisfies $h_G(n) \gg n$, since it contains
infinitely many vertex-disjoint odd cycles of some fixed length $2r+1$. -/
@[category research solved, AMS 5]
theorem erdos_111.variants.linear_lower_bound (G : SimpleGraph V)
    (hG : G.chromaticCardinal = ℵ_ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * n ≤ (h G n : ℝ) := by
  sorry

/-- Erdős, Hajnal and Szemerédi [EHS82] constructed a graph $G$ with chromatic number $\aleph_1$
such that $h_G(n) \ll n^{3/2}$. -/
@[category research solved, AMS 5]
theorem erdos_111.variants.three_halves :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 ∧
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (h G n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

/-- Erdős [Er81] conjectured that for every $\epsilon > 0$ there is a graph $G$ with chromatic
number $\aleph_1$ such that $h_G(n) \ll n^{1+\epsilon}$. -/
@[category research open, AMS 5]
theorem erdos_111.variants.one_add_eps :
    answer(sorry) ↔ ∀ ε : ℝ, 0 < ε → ∃ (V : Type) (G : SimpleGraph V),
      G.chromaticCardinal = ℵ_ 1 ∧
        ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (h G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) := by
  sorry

end Erdos111
