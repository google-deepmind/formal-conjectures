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
# Erdős Problem 65

*References:*
- [erdosproblems.com/65](https://www.erdosproblems.com/65)
- [GKS84] Gyárfás, A., Komlós, J. and Szemerédi, E., On the distribution of cycle lengths in graphs.
  J. Graph Theory (1984), 441-462.
- [LiMo20] Liu, H. and Montgomery, R., A solution to Erdős and Hajnal's odd cycle problem.
  arXiv:2010.15802 (2020).
-/

namespace Erdos65

/--
Let $G$ be a graph with $n$ vertices and $kn$ edges, and $a_1<a_2<\cdots$ be the lengths of
cycles in $G$. Assume $n>0$ and $k>0$. Is it true that
$$\sum\frac{1}{a_i}\gg \log k?$$

Gyárfás, Komlós, and Szemerédi [GKS84] have proved that this sum is $\gg \log k$, so that only
the second question remains.
-/
@[category research solved, AMS 5]
theorem erdos_65.parts.i : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (k : ℝ) (hk : 0 < k),
      ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        0 < n →
        Fintype.card V = n →
        (G.edgeSet.ncard : ℝ) = k * n →
        (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) ≥ c * Real.log k := by
  sorry

/--
Is the sum $\sum\frac{1}{a_i}$ minimised when $G$ is a complete bipartite graph?

This problem is #65 in Extremal Graph Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_65.parts.ii : answer(sorry) ↔
    ∀ (k : ℝ) (hk : 0 < k),
      ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        0 < n →
        Fintype.card V = n →
        (G.edgeSet.ncard : ℝ) = k * n →
        ∀ (A B : Type) [Fintype A] [Fintype B],
          Fintype.card (A ⊕ B) = n →
          ((completeBipartiteGraph A B).edgeSet.ncard : ℝ) = k * n →
          (∑ᶠ a ∈ (completeBipartiteGraph A B).cycleLengths, (1 : ℝ) / a) ≤
            (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos65
