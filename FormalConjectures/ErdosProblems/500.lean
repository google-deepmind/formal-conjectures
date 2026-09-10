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
# Erdős Problem 500

*References:*
- [erdosproblems.com/500](https://www.erdosproblems.com/500)
- [Ra10] Razborov, Alexander A., On 3-hypergraphs with forbidden 4-vertex configurations. SIAM J.
Discrete Math. (2010), 946-963.
-/

namespace Erdos500

open Filter Asymptotics

/--
What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can placed on $n$
vertices so that there exists no $K_4^3$, a set of 4 vertices which is covered by all 4 possible
$3$-edges.
-/
@[category research open, AMS 5]
theorem erdos_500 :
    (fun n ↦ Hypergraph.cliqueExtremalNumber n 3 4) = answer(sorry) := by
  sorry

end Erdos500
