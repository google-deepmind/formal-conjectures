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
# Erdős Problem 87

*References:*
- [erdosproblems.com/87](https://www.erdosproblems.com/87)
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open Filter

namespace Erdos87

/--
Let $\epsilon > 0$. Is it true that, if $k$ is sufficiently large, then
$$R(G) > (1-\epsilon)^k R(k)$$
for every graph $G$ with chromatic number $\chi(G)=k$?
-/
@[category research open, AMS 5]
theorem erdos_87 : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.chromaticNumber = (k : ℕ∞) →
        (SimpleGraph.diagonalGraphRamsey G : ℝ) > (1 - ε) ^ k * (SimpleGraph.diagonalRamsey k : ℝ) := by
  sorry

/--
Even stronger, is there some $c > 0$ such that, for all large $k$,
$$R(G) > c R(k)$$
for every graph $G$ with chromatic number $\chi(G)=k$?
-/
@[category research open, AMS 5]
theorem erdos_87.parts.stronger : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.chromaticNumber = (k : ℕ∞) →
        (SimpleGraph.diagonalGraphRamsey G : ℝ) > c * (SimpleGraph.diagonalRamsey k : ℝ) := by
  sorry

end Erdos87
