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
# Erdős Problem 716

*References:*
- [erdosproblems.com/716](https://www.erdosproblems.com/716)
- [BES73] Brown, W. G. and Erdős, P. and S\'os, V. T., Some extremal problems on {$r$}-graphs.
(1973), 53--63.
- [RuSz78] Ruzsa, I. Z. and Szemer\'{e}di, E., Triple systems with no six points carrying three
triangles. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978), 939-945.
-/

namespace Erdos716

open Filter Asymptotics

/--
Let $\mathcal{F}$ be the family of all $3$-uniform hypergraphs with $6$ vertices and $3$ $3$-edges.
Is it true that
$$\mathrm{ex}_3(n,\mathcal{F})=o(n^2)?$$

The answer is yes, proved by Ruzsa and Szemerédi [RuSz78] (this is known as the Ruzsa-Szemerédi
problem).
-/
@[category research solved, AMS 5]
theorem erdos_716 :
    answer(True) ↔
    (fun n ↦ (Hypergraph.configurationExtremalNumber n 3 6 3 : ℝ)) =o[atTop]
      (fun n ↦ (n : ℝ) ^ 2) := by
  sorry

end Erdos716
