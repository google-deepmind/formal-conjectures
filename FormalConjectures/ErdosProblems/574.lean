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
# Erdős Problem 574

*Reference:* [erdosproblems.com/574](https://www.erdosproblems.com/574)

A problem of Erdős and Simonovits.

[ErSi82] Erdős, P. and Simonovits, M.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos574

/-- A simple graph $G$ contains a cycle of length $m$ ($m \geq 3$) if there exist $m$
distinct vertices $v_0, \ldots, v_{m-1}$ such that $v_i$ is adjacent to
$v_{(i+1) \bmod m}$ for all $i$. -/
def ContainsCycleOfLength {V : Type*} (G : SimpleGraph V) (m : ℕ) (_ : m ≥ 3) : Prop :=
  ∃ (f : Fin m → V), Function.Injective f ∧
    ∀ i j : Fin m, j.val = (i.val + 1) % m → G.Adj (f i) (f j)

/-- The extremal number $\operatorname{ex}(n; \{C_{2k-1}, C_{2k}\})$: the maximum number of edges
in a simple graph on $n$ vertices containing no cycle of length $2k-1$ or $2k$. -/
noncomputable def exConsecutiveCycles (k : ℕ) (hk : k ≥ 2) (n : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsCycleOfLength G (2 * k - 1) (by omega) ∧
    ¬ContainsCycleOfLength G (2 * k) (by omega) ∧
    G.edgeSet.ncard = e}

/--
Erdős Problem 574:
Is it true that, for $k \geq 2$,
$$\operatorname{ex}(n; \{C_{2k-1}, C_{2k}\}) = (1 + o(1)) \cdot (n/2)^{1 + 1/k}?$$

The extremal number $\operatorname{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the maximum number of edges in
a graph on $n$ vertices that contains no cycle of length $2k-1$ and no cycle of length $2k$.

The conjecture asserts that for each fixed $k \geq 2$, this extremal number is
asymptotically $(n/2)^{1+1/k}$, i.e. the ratio tends to $1$ as $n \to \infty$.

The case $k = 2$ (forbidding $C_3$ and $C_4$) is Erdős Problem 573.

[ErSi82]
-/
@[category research open, AMS 5]
theorem erdos_574 : answer(sorry) ↔
    ∀ (k : ℕ) (hk : k ≥ 2), Tendsto
      (fun n : ℕ => (exConsecutiveCycles k hk n : ℝ) / ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ)))
      atTop (nhds 1) := by
  sorry

end Erdos574
