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
# Erdős Problem 24

*References:*
- [erdosproblems.com/24](https://www.erdosproblems.com/24)
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) (1992), 231-240.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [Gr12] Grzesik, Andrzej, *On the maximum number of five-cycles in a triangle-free graph*.
  J. Combin. Theory Ser. B (2012), 1061-1066.
- [HHKNR13] Hatami, Hamed and Hladký, Jan and Kráľ, Daniel and Norine, Serguei and Razborov,
  Alexander, *On the number of pentagons in triangle-free graphs*. J. Combin. Theory Ser. A
  (2013), 722-732.
-/

open SimpleGraph

namespace Erdos24

/--
Does every triangle-free graph on $5n$ vertices contain at most $n^5$ copies of $C_5$?

Győri proved this with $1.03n^5$, which has been improved by Füredi. The answer is yes, as proved
independently by Grzesik [Gr12] and Hatami, Hladky, Král, Norine, and Razborov [HHKNR13].

Copies of $C_5$ are counted as subgraphs isomorphic to the cycle graph on five vertices,
i.e. by `SimpleGraph.copyCount`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos24.lean"]
theorem erdos_24 : answer(True) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))), G.CliqueFree 3 →
      G.copyCount (cycleGraph 5) ≤ n ^ 5 := by
  sorry

end Erdos24
