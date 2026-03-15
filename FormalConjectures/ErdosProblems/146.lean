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
# Erdős Problem 146

Erdős and Simonovits conjectured that the Turán number of any $r$-degenerate bipartite
graph $H$ satisfies $\text{ex}(n; H) = O(n^{2 - 1/r})$.

See also problems #113 and #147 for related conjectures on Turán numbers of degenerate
bipartite graphs.

*Reference:* [erdosproblems.com/146](https://www.erdosproblems.com/146)

[ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related
problems*, Progress in graph theory (Waterloo, Ont., 1982), Academic Press,
Toronto, ON, 1984, 203-218.

[Er91] Erdős, P., *Problems and results on graphs and hypergraphs: similarities and
differences*. Mathematics of Ramsey theory, Algorithms Combin., 5 (1990), 12-28.

[Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
Quaestiones Mathematicae **16** (1993), 333–350.

[Er97c] Erdős, P., *Some recent problems and results in graph theory*. Discrete Math.
**164** (1997), 81–85.

[AKS03] Alon, N., Krivelevich, M., and Sudakov, B., *Turán numbers of bipartite
graphs and related Ramsey-type questions*, Combinatorics, Probability and
Computing 12 (2003), no. 5-6, 477-494.
-/

open SimpleGraph

namespace Erdos146

/-- A graph $G$ is $r$-degenerate if every non-empty finite set of vertices contains
a vertex with at most $r$ neighbors within that set. Equivalently, every induced
subgraph of $G$ has minimum degree at most $r$. -/
def IsRDegenerateGraph {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ r

/--
Erdős-Simonovits Conjecture (Problem #146) [ErSi84]:
If $H$ is a bipartite graph that is $r$-degenerate (i.e., every induced subgraph of $H$
has minimum degree at most $r$), then
$$\text{ex}(n; H) \ll n^{2 - 1/r}.$$
That is, there exists a constant $C > 0$ such that $\text{ex}(n; H) \leq C \cdot n^{2 - 1/r}$
for all $n \geq 1$.

This is open even for $r = 2$. Alon, Krivelevich, and Sudakov [AKS03] proved the
weaker bound $\text{ex}(n; H) \ll n^{2 - 1/(4r)}$.
-/
@[category research open, AMS 5]
theorem erdos_146 :
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      IsRDegenerateGraph H r →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (extremalNumber n H : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) := by
  sorry

end Erdos146
