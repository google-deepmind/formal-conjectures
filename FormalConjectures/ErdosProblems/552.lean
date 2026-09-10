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
# Erdős Problem 552

*References:*
- [erdosproblems.com/552](https://www.erdosproblems.com/552)
- [BEFRS89] Burr, S. and Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Some
  complete bipartite graph-tree Ramsey numbers. Graph theory in memory of G. A. Dirac (Sandbjerg,
  1985) (1989), 79-89.
-/

namespace Erdos552

/--
Determine the Ramsey number
$$R(C_4, S_n),$$
where $S_n=K_{1,n}$ is the star on $n+1$ vertices.

A problem of Burr, Erdős, Faudree, Rousseau, and Schelp [BEFRS89].

This problem is #19 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_552.parts.i :
    ∀ (n : ℕ),
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) =
        answer(sorry) := by
  sorry

/--
In particular, is it true that, for any $c > 0$, there are infinitely many $n$ such that
$$R(C_4, S_n) \leq n + \sqrt{n} - c?$$
-/
@[category research open, AMS 5]
theorem erdos_552.parts.ii : answer(sorry) ↔
    ∀ (c : ℝ), 0 < c →
      Set.Infinite {n : ℕ |
        (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
          (completeBipartiteGraph (Fin 1) (Fin n)) : ℝ) ≤ (n : ℝ) + Real.sqrt n - c} := by
  sorry

-- TODO: Add variants of the problem.

end Erdos552
