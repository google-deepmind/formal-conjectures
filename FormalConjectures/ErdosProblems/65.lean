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
- [ErHa66] Erdős, P. and Hajnal, A., On chromatic number of graphs and set-systems. Acta Math. Acad.
  Sci. Hungar. (1966), 61-99.
- [GKS84] Gyárfás, A., Komlós, J. and Szemerédi, E., On the cycle lengths of graphs. J. Graph Theory
  (1984), 441-445.
- [LiMo20] Liu, C. and Montgomery, R., A solution to Erdős and Hajnal's odd cycle problem.
  arXiv:2010.15844 (2020).
-/

namespace Erdos65

/--
Let $G$ be a graph with $n$ vertices and $kn$ edges, and $a_1<a_2<\cdots$ be the lengths of
cycles in $G$. Is it true that
$$\sum\frac{1}{a_i}\gg \log k?$$

Gyárfás, Komlós, and Szemerédi [GKS84] proved that $\sum \frac{1}{a_i} \gg \log k$.
-/
@[category research solved, AMS 5]
theorem erdos_65.parts.gks : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (k : ℕ) (hk : 2 ≤ k),
      ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n →
        G.edgeSet.ncard = k * n →
        (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) ≥ c * Real.log k := by
  sorry

/--
Is the sum $\sum\frac{1}{a_i}$ minimised when $G$ is a complete bipartite graph?
-/
@[category research open, AMS 5]
theorem erdos_65 : answer(sorry) ↔
    ∀ (k : ℕ) (hk : 2 ≤ k),
      ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n →
        G.edgeSet.ncard = k * n →
        ∀ (A B : Type) [Fintype A] [Fintype B] (K : SimpleGraph (A ⊕ B)),
          K = completeBipartiteGraph A B →
          Fintype.card (A ⊕ B) = n →
          K.edgeSet.ncard = k * n →
          (∑ᶠ a ∈ K.cycleLengths, (1 : ℝ) / a) ≤ (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) := by
  sorry

end Erdos65
