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
# Erdős Problem 573

*Reference:* [erdosproblems.com/573](https://www.erdosproblems.com/573)

Is it true that $\operatorname{ex}(n; \{C_3, C_4\}) \sim (n/2)^{3/2}$?

This is the $k = 2$ case of [Erdős Problem 574](https://www.erdosproblems.com/574).
See also [Erdős Problem 765](https://www.erdosproblems.com/765) concerning
$\operatorname{ex}(n; C_4)$ specifically.

OEIS: [A006856](https://oeis.org/A006856)

[Er71] Erdős, P., *Topics in combinatorial analysis*, 1971, p.103.
[Er75] Erdős, P., *Problems and results on combinatorial number theory*, 1975.
[ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
Combinatorica **2** (1982), 275-288.
[Er93] Erdős, P., 1993, p.336.
[KST54] Kővári, T., Sós, V. T., and Turán, P., *On a problem of K. Zarankiewicz*.
Colloq. Math. **3** (1954), 50-57.
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos573

/-- A simple graph is $C_4$-free if it contains no 4-cycle.
The conditions $a \neq c$ and $b \neq d$ ensure the four vertices are distinct
(the remaining distinctness conditions follow from irreflexivity of `Adj`). -/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a

/-- The extremal number $\operatorname{ex}(n; \{C_3, C_4\})$: the maximum number of edges in a
simple graph on $n$ vertices containing neither a triangle ($C_3$, i.e. a $3$-clique)
nor a 4-cycle ($C_4$). -/
noncomputable def exC3C4 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 3 ∧ C4Free G ∧ G.edgeSet.ncard = k}

/--
Is it true that $\operatorname{ex}(n; \{C_3, C_4\}) \sim (n/2)^{3/2}$?

The extremal number $\operatorname{ex}(n; \{C_3, C_4\})$ is the maximum number of edges in a graph
on $n$ vertices that contains no triangle ($C_3$) and no 4-cycle ($C_4$).

The conjecture asserts that this quantity is asymptotically $(n/2)^{3/2}$,
i.e. the ratio $\operatorname{ex}(n; \{C_3, C_4\}) / (n/2)^{3/2}$ tends to $1$ as $n \to \infty$.

Erdős and Simonovits proved that $\operatorname{ex}(n; \{C_4, C_5\}) = (n/2)^{3/2} + O(n)$.
Kővári, Sós, and Turán proved that the extremal number for forbidding $C_4$
together with any odd cycle is $\sim (n/2)^{3/2}$. This problem asks whether
the same holds when only $C_3$ (triangles) are forbidden alongside $C_4$.

References: [Er71,p.103], [Er75], [ErSi82], [Er93,p.336], [KST54]
-/
@[category research open, AMS 5]
theorem erdos_573 :
    answer(sorry) ↔
      Tendsto
        (fun n : ℕ => (exC3C4 n : ℝ) / ((n : ℝ) / 2) ^ ((3 : ℝ) / 2))
        atTop (nhds 1) := by
  sorry

end Erdos573
