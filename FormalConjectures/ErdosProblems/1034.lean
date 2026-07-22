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
# Erdős Problem 1034

*References:*
- [erdosproblems.com/1034](https://www.erdosproblems.com/1034)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [MaTa25] Ma, Jie and Tang, Quanyu, *On Erdős problem #1034*.
  [staff.ustc.edu.cn/~jiema/Erdos-1034.pdf](http://staff.ustc.edu.cn/~jiema/Erdos-1034.pdf)
-/

open Classical Filter

namespace Erdos1034

/--
`JoinedToTwo G T Y` holds when every vertex of `Y` is joined to at least two (distinct)
vertices of `T`.
-/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

/--
Let $G$ be a graph on $n$ vertices with $>n^2/4$ many edges. Must there be a triangle $T$ in $G$
and vertices $y_1,\ldots,y_t$, where $t>(\frac{1}{2}-o(1))n$, such that every $y_i$ is joined to
at least two vertices of $T$?

A conjecture of Erdős and Faudree; a stronger version of [905].

This has been solved in the negative by Ma and Tang [MaTa25], who construct a graph with $n$
vertices and $>n^2/4$ edges in which every triangle has at most $(2-(5/2)^{1/2}+o(1))n$ vertices
adjacent to at least two of its vertices (note that $2-(5/2)^{1/2}\approx 0.4189$).
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1034.lean"]
theorem erdos_1034 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 2 - ε) * (n : ℝ) < (Y.card : ℝ) := by
  sorry

/--
Erdős and Faudree asked about the threshold $h(n)$ such that every graph with $n$ vertices and
$>n^2/4$ edges contained a triangle and $h(n)$ other vertices which are connected to at least two
vertices of the triangle. The fact that every graph with $>n^2/4$ edges contains a book of size
$n/6$ shows that
\[(1/6-o(1))n \leq h(n).\]
-/
@[category research solved, AMS 5]
theorem erdos_1034.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ) := by
  sorry

/--
The construction of Ma and Tang [MaTa25] of a graph with $n$ vertices and $>n^2/4$ edges in which
every triangle has at most $(2-(5/2)^{1/2}+o(1))n$ vertices adjacent to at least two of its
vertices shows that, for the threshold $h(n)$ of `erdos_1034.variants.lower_bound`,
\[h(n) \leq (2-(5/2)^{1/2}+o(1))n.\]
-/
@[category research solved, AMS 5]
theorem erdos_1034.variants.upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y → (Y.card : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ) := by
  sorry

/--
Erdős suggested that the answer is different if $G$ has no $K_4$. In the comments Ma and Tang
sketch a proof that the conjecture remains false even if we assume that $G$ contains no $K_4$,
constructing a graph with $n$ vertices, $>n^2/4$ edges, and no $K_4$, in which every triangle has
at most $(2\sqrt{3}-3+o(1))n$ vertices adjacent to at least two of its vertices (note that
$2\sqrt{3}-3\approx 0.464$).
-/
@[category research solved, AMS 5]
theorem erdos_1034.variants.k4_free (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y → (Y.card : ℝ) ≤ (2 * Real.sqrt 3 - 3 + ε) * (n : ℝ) := by
  sorry

end Erdos1034
