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
# Erdős Problem 637

*Reference:* [erdosproblems.com/637](https://www.erdosproblems.com/637)

If $G$ is a graph on $n$ vertices which contains no complete graph or independent
set on $\gg \log n$ vertices then $G$ contains an induced subgraph on $\gg n$ vertices
which contains $\gg n^{1/2}$ distinct degrees.

A problem of Erdős, Faudree, and Sós [Er97d].

This was proved by Bukh and Sudakov [BuSu07].

Jenssen, Keevash, Long, and Yepremyan [JKLY20] proved that there must exist
an induced subgraph which contains $\gg n^{2/3}$ distinct degrees (with no
restriction on the number of vertices).

[Er97d] Erdős, P., _Some of my favourite problems in various branches of
combinatorics_, 1997.

[BuSu07] Bukh, B. and Sudakov, B., _Induced subgraphs of Ramsey graphs with
many distinct degrees_, 2007.

[JKLY20] Jenssen, M., Keevash, P., Long, E. and Yepremyan, L., _Distinct
degrees in induced subgraphs_, 2020.
-/

open SimpleGraph Classical

namespace Erdos637

/-- The degree of vertex $v$ in the induced subgraph $G[S]$. -/
noncomputable def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter fun w => G.Adj v w).card

/-- The number of distinct degrees realized by vertices of $S$ in the induced
    subgraph $G[S]$. -/
noncomputable def inducedDistinctDegrees {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (S.image fun v => inducedDegree G S v).card

/--
**Erdős Problem 637** (PROVED) [Er97d]:

For every $C > 0$, there exist $c_1 > 0$, $c_2 > 0$, and $N_0$ such that for all
$n \geq N_0$, if $G$ is a graph on $n$ vertices with clique number at most
$C \cdot \log_2(n)$ and independence number at most $C \cdot \log_2(n)$, then there
exists a subset $S$ of vertices with $|S| \geq c_1 \cdot n$ such that the induced
subgraph $G[S]$ has at least $c_2 \cdot n^{1/2}$ distinct degrees.

Proved by Bukh and Sudakov [BuSu07].
-/
@[category research solved, AMS 5]
theorem erdos_637 :
    ∀ C : ℝ, C > 0 →
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    ∃ S : Finset (Fin n), (S.card : ℝ) ≥ c₁ * (↑n : ℝ) ∧
      (inducedDistinctDegrees G S : ℝ) ≥ c₂ * (↑n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos637
