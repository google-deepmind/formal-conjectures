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
# Erdős Problem 1076

*References:*
- [erdosproblems.com/1076](https://www.erdosproblems.com/1076)
- [BES73] Brown, W. G. and Erdős, P. and S\'os, V. T., Some extremal problems on {$r$}-graphs.
(1973), 53--63.
- [BoWa19] Bohman, Tom and Warnke, Lutz, Large girth approximate Steiner triple systems. J. Lond.
Math. Soc. (2) (2019), 895--913.
- [Er74c] Erdős, Paul, Extremal problems on graphs and hypergraphs. (1974), 75-84.
- [GKLO20] Glock, Stefan and K\"uhn, Daniela and Lo, Allan and Osthus, Deryk, On a conjecture of
{E}rdős on locally sparse Steiner triple systems. Combinatorica (2020), 363--403.
-/

namespace Erdos1076

open Filter Asymptotics

/--
Let $k\geq 5$ and let $\mathcal{F}_k$ be the family of all $3$-uniform hypergraphs with $k$ vertices
and $k-2$ edges. Is it true that
$$\mathrm{ex}_3(n,\mathcal{F}_k)\sim \frac{n^2}{6}?$$

The asymptotic version asked for here was proved independently by Bohman and Warnke [BoWa19] and
Glock, Kühn, Lo, and Osthus [GKLO20].
-/
@[category research solved, AMS 5]
theorem erdos_1076 :
    answer(True) ↔ ∀ k : ℕ, 5 ≤ k →
    (fun n ↦ (Hypergraph.configurationExtremalNumber n 3 k (k - 2) : ℝ)) ~[atTop]
      (fun n ↦ (n : ℝ) ^ 2 / 6) := by
  sorry

end Erdos1076
