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
# Erdős Problem 901

*References:*
- [erdosproblems.com/901](https://www.erdosproblems.com/901)
- [Be77] Beck, J., On a combinatorial problem of {P}. {E}rdős and {L}. {L}ovász. Discrete Math.
  (1977), 127--131.
- [Be78] Beck, J., On {$3$}-chromatic hypergraphs. Discrete Math. (1978), 127--137.
- [Er63b] Erdős, P., On a combinatorial problem. Nordisk Mat. Tidskr. (1963), 5--10, 40.
- [Er64e] Erdős, P., On a combinatorial problem. {II}. Acta Math. Acad. Sci. Hungar. (1964),
  445--447.
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
- [Pl09] Pluhár, András, Greedy colorings of uniform hypergraphs. Random Structures Algorithms
  (2009), 216--221.
- [RaSr00] Radhakrishnan, Jaikumar and Srinivasan, Aravind, Improved bounds and algorithms for
  hypergraph {$2$}-coloring. Random Structures Algorithms (2000), 4--32.
-/

namespace Erdos901

open Filter Asymptotics

/--
Let $m(n)$ be minimal such that there is an $n$-uniform hypergraph with $m(n)$ edges which is
$3$-chromatic. Estimate $m(n)$.
-/
@[category research open, AMS 5]
theorem erdos_901 :
    (fun n ↦ ((Hypergraph.minChromaticEdges n 3).toNat : ℝ)) =Θ[atTop]
    (answer(sorry) : ℕ → ℝ) := by
  sorry

end Erdos901
