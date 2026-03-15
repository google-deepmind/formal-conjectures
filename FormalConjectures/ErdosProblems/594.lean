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
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Copy
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 594

*Reference:* [erdosproblems.com/594](https://www.erdosproblems.com/594)

A problem of Erdős and Hajnal: does every graph with chromatic number
$\geq \aleph_1$ contain all sufficiently large odd cycles? Proved by
Erdős, Hajnal, and Shelah [EHS74].

[ErHa66] Erdős, P. and Hajnal, A., *On chromatic number of graphs and
set-systems*, Acta Math. Acad. Sci. Hung. **17** (1966), 61–99.

[Er69b] Erdős, P., *Problems and results in combinatorial analysis and
graph theory*, Proof Techniques in Graph Theory (1969), 27–35.

[EHS74] Erdős, P., Hajnal, A., and Shelah, S., *On some general properties
of chromatic numbers*, Topics in Topology, Colloq. Math. Soc. Janos Bolyai
**8** (1974), 243–255.
-/

open SimpleGraph Cardinal

namespace Erdos594

/--
Erdős Problem 594 [ErHa66] [Er69b]:

Every graph with uncountable chromatic number (i.e., chromatic number
$\geq \aleph_1$) contains all sufficiently large odd cycles. That is, there exists
$N_0$ such that for all odd $n \geq N_0$, the graph contains $C_n$
as a subgraph.

Proved by Erdős, Hajnal, and Shelah [EHS74].
-/
@[category research solved, AMS 5]
theorem erdos_594 : answer(True) ↔
    ∀ {V : Type*} (G : SimpleGraph V),
      Cardinal.aleph 1 ≤ G.chromaticCardinal →
      ∃ N₀ : ℕ, ∀ (n : ℕ), Odd n → n ≥ N₀ →
        (cycleGraph n).IsContained G := by
  sorry

end Erdos594
