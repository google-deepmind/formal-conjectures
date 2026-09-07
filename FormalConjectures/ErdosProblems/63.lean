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
# Erdős Problem 63

*References:*
- [erdosproblems.com/63](https://www.erdosproblems.com/63)
- [dBEr51] de Bruijn, N. G. and Erdős, P., *A colour problem for infinite graphs and a problem
  in the theory of relations*. Indag. Math. (1951), 369--373.
- [ErHa66] Erdős, P. and Hajnal, A., *On chromatic number of graphs and set-systems*.
  Acta Math. Acad. Sci. Hungar. (1966), 61-99.
- [LiMo20] Liu, Hong and Montgomery, Richard, *A solution to Erdős and Hajnal's odd cycle problem*.
  arXiv:2010.15802 (2020).
- [Re24] Reiher, C., *Graphs of large girth*. arXiv:2403.13571 (2024).
-/

namespace Erdos63

/--
Does every graph with infinite chromatic number contain a cycle of length $2^n$ for infinitely
many $n$?

Conjectured by Mihók and Erdős. Solved affirmatively following the work of Liu and Montgomery
[LiMo20].
-/
@[category research solved, AMS 5]
theorem erdos_63 :
    answer(True) ↔
      ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
        ∀ N : ℕ, ∃ n ≥ N, 2 ^ n ∈ G.cycleLengths := by
  sorry

-- TODO: Add variants of the problem.

end Erdos63
