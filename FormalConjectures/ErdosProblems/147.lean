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
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/-!
# Erdős Problem 147

*Reference:* [erdosproblems.com/147](https://www.erdosproblems.com/147)

See also problems #113, #146, and #714 for related conjectures on Turán numbers of
bipartite graphs.

[ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_,
Progress in graph theory (Waterloo, Ont., 1982), Academic Press, Toronto, ON, 1984, 203–218.

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Ja23] Janzer, O., _Rainbow Turán number of even cycles, repeated patterns and blow-ups
of cycles_. Israel J. Math. (2023), 813–840.

[Ja23b] Janzer, O., _Disproof of a conjecture of Erdős and Simonovits on the Turán number
of graphs with minimum degree 3_. Int. Math. Res. Not. IMRN (2023), 8478–8494.
-/

open SimpleGraph

namespace Erdos147

/--
Erdős Problem 147 [ErSi84]:
If $H$ is a bipartite graph with minimum degree $r$ (i.e., every vertex of $H$ has
degree at least $r$, where $r \geq 2$), is it true that there exists
$\varepsilon = \varepsilon(H) > 0$ such that
$$
\mathrm{ex}(n; H) \gg n^{2 - 1/(r-1) + \varepsilon}?
$$
That is, do there exist constants $C > 0$ and $N_0 \in \mathbb{N}$ such that for all $n \geq N_0$:
$$
\mathrm{ex}(n; H) \geq C \cdot n^{2 - 1/(r-1) + \varepsilon}?
$$

This conjecture was **disproved**: Janzer [Ja23] disproved it for even $r \geq 4$, and
[Ja23b] disproved it for $r = 3$, constructing for any $\delta > 0$ a $3$-regular bipartite
graph $H$ with $\mathrm{ex}(n; H) \ll n^{4/3 + \delta}$.
-/
@[category research solved, AMS 5]
theorem erdos_147 : answer(False) ↔
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (extremalNumber n H : ℝ) := by
  sorry

end Erdos147
