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
# Erdős Problem 65

*Reference:* [erdosproblems.com/65](https://www.erdosproblems.com/65)

Is the sum of reciprocals of distinct cycle lengths in a graph on $n$ vertices with $kn$
edges minimised by the complete bipartite graph? Gyárfás, Komlós, and Szemerédi [GKS84]
proved $\sum 1/a_i \gg \log k$; Liu and Montgomery [LiMo20] proved the sharp bound.

[GKS84] Gyárfás, A., Komlós, J., and Szemerédi, E., *On the distribution of cycle lengths in
graphs*, J. Graph Theory 8 (1984), 441–462.

[LiMo20] Liu, H. and Montgomery, R., *A solution to Erdős and Hajnal's odd cycle problem*,
J. Amer. Math. Soc. 36 (2023), 1191–1234.
-/

open SimpleGraph Finset

namespace Erdos65

/-- The complete bipartite graph $K_{a,b}$ on `Fin (a + b)`, where vertices
$\{0, \ldots, a-1\}$ form one part and $\{a, \ldots, a+b-1\}$ form the other. -/
def completeBipartiteGraph65 (a b : ℕ) : SimpleGraph (Fin (a + b)) where
  Adj u v := (u.val < a ∧ a ≤ v.val) ∨ (a ≤ u.val ∧ v.val < a)
  symm u v h := by
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  loopless v h := by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/--
Erdős Problem #65 (Erdős–Hajnal) [GKS84] [LiMo20]:
Let $G$ be a graph with $n$ vertices and $kn$ edges, and let $a_1 < a_2 < \cdots$ be the
distinct lengths of cycles in $G$. Is it true that $\sum 1/a_i \gg \log k$? Is the sum
$\sum 1/a_i$ minimised when $G$ is a complete bipartite graph?

The first question was proved by Gyárfás, Komlós, and Szemerédi [GKS84].
Liu and Montgomery [LiMo20] proved the asymptotically sharp lower bound
$\geq (1/2 - o(1)) \log k$.

The remaining open question is formalized below: for any graph $G$ on $n$ vertices whose edge
count equals $a \cdot b$ for some partition $a + b = n$, the sum of reciprocals of distinct cycle
lengths of $G$ is at least the corresponding sum for the complete bipartite graph $K_{a,b}$.
-/
@[category research open, AMS 5]
theorem erdos_65 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (a b : ℕ), a + b = n →
      ∀ [DecidableRel G.Adj], a * b = G.edgeFinset.card →
      ∀ (T_G : Finset ℕ),
        (∀ m ∈ T_G, ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) →
        (∀ m : ℕ, (∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_G) →
        ∃ (T_K : Finset ℕ),
          (∀ m ∈ T_K, ∃ v : Fin (a + b),
            ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) ∧
          (∀ m : ℕ, (∃ v : Fin (a + b),
            ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_K) ∧
          ∑ m ∈ T_K, (1 / (m : ℝ)) ≤ ∑ m ∈ T_G, (1 / (m : ℝ)) := by
  sorry

end Erdos65
