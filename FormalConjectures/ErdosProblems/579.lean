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
# Erdős Problem 579

Erdős, Hajnal, Sós, and Szemerédi conjectured that for any δ > 0, if n is sufficiently large
and G is a K_{2,2,2}-free graph on n vertices with at least δn² edges, then G contains an
independent set of size linear in n.

*Reference:* [erdosproblems.com/579](https://www.erdosproblems.com/579)
-/

open SimpleGraph

namespace Erdos579

/-- A graph $G$ on vertex type $V$ contains $K_{2,2,2}$ (the complete tripartite graph
with three parts of size $2$, also known as the octahedron) if there exist $6$ distinct
vertices partitioned into $3$ pairs with all cross-pair edges present. -/
def ContainsK222 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a₁ a₂ b₁ b₂ c₁ c₂ : V),
    -- All 6 vertices are distinct
    a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ c₁ ≠ c₂ ∧
    a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₁ ≠ c₁ ∧ a₁ ≠ c₂ ∧
    a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧ a₂ ≠ c₁ ∧ a₂ ≠ c₂ ∧
    b₁ ≠ c₁ ∧ b₁ ≠ c₂ ∧ b₂ ≠ c₁ ∧ b₂ ≠ c₂ ∧
    -- All edges between parts A and B
    G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₂ b₁ ∧ G.Adj a₂ b₂ ∧
    -- All edges between parts A and C
    G.Adj a₁ c₁ ∧ G.Adj a₁ c₂ ∧ G.Adj a₂ c₁ ∧ G.Adj a₂ c₂ ∧
    -- All edges between parts B and C
    G.Adj b₁ c₁ ∧ G.Adj b₁ c₂ ∧ G.Adj b₂ c₁ ∧ G.Adj b₂ c₂

/--
Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no
$K_{2,2,2}$ and at least $\delta n^2$ edges then $G$ contains an independent set of size
$\gg_\delta n$.

A problem of Erdős, Hajnal, Sós, and Szemerédi, who proved this for $\delta > 1/8$.
-/
@[category research open, AMS 5]
theorem erdos_579 :
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℝ, 0 < c ∧
        ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n →
            ∀ G : SimpleGraph (Fin n),
              ¬ContainsK222 G →
              δ * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) →
                ∃ S : Finset (Fin n),
                  c * (n : ℝ) ≤ (S.card : ℝ) ∧
                  (G.induce (S : Set (Fin n))).CliqueFree 2 := by
  sorry

end Erdos579
