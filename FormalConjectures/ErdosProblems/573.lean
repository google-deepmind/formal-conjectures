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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 573

*References:*
- [erdosproblems.com/573](https://www.erdosproblems.com/573)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica (1982), 275-288.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [KST54] Kővári, T. and Sós, V. T. and Turán, P., *On a problem of K. Zarankiewicz*.
  Colloq. Math. (1954), 50-57.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos573

open scoped Classical in
/-- $\mathrm{ex}(n;\{C_k : k \in L\})$: the greatest number of edges of a simple graph on `n`
vertices that contains no cycle $C_k$ with $k \in L$ as a (not necessarily induced) subgraph.

`cycleGraph k` is the cycle on `Fin k`. The definition is meaningful only for sets `L` of
lengths `k ≥ 3`, which are the only ones used below: `cycleGraph 0` and `cycleGraph 1` have no
edges, and `cycleGraph 2` is a single edge. -/
noncomputable def cycleExtremalNumber (L : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => ∀ k ∈ L, (cycleGraph k).Free G).sup
    fun G => G.edgeFinset.card

/--
Is it true that
$$\mathrm{ex}(n;\{C_3,C_4\})\sim (n/2)^{3/2}?$$

A problem of Erdős and Simonovits. This problem is asking whether the threshold is the same as
for forbidding $C_4$ and all odd cycles (see `erdos_573.variants.kst`) if one only forbids the odd
cycle of length $3$. See also [574] for the general case, and [765] for $\mathrm{ex}(n;C_4)$.

This problem is #48 in Extremal Graph Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_573 : answer(sorry) ↔
    (fun n : ℕ ↦ (cycleExtremalNumber {3, 4} n : ℝ)) ~[atTop]
      fun n : ℕ ↦ ((n : ℝ) / 2) ^ (3 / 2 : ℝ) := by
  sorry

/--
Erdős and Simonovits [ErSi82] proved that
$$\mathrm{ex}(n;\{C_4,C_5\})=(n/2)^{3/2}+O(n).$$

Here $O(n)$ is an upper error term, so we state the upper bound
$\mathrm{ex}(n;\{C_4,C_5\}) \leq (n/2)^{3/2} + O(n)$. A matching lower bound up to $O(n)$ is not
known for every $n$: the known constructions come from projective planes and lose more than
$O(n)$ edges when $n$ is not of a special form.
-/
@[category research solved, AMS 5]
theorem erdos_573.variants.c4_c5 :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (cycleExtremalNumber {4, 5} n : ℝ) ≤ ((n : ℝ) / 2) ^ (3 / 2 : ℝ) + C * n := by
  sorry

/--
Kővári, Sós, and Turán [KST54] proved that the extremal number of edges for containing either
$C_4$ or an odd cycle of any length is $\sim (n/2)^{3/2}$, that is,
$$\mathrm{ex}(n;\{C_4, C_3, C_5, C_7, \ldots\})\sim (n/2)^{3/2}.$$
Equivalently, the maximum number of edges of a bipartite $C_4$-free graph on $n$ vertices is
$\sim (n/2)^{3/2}$. The attribution follows erdosproblems.com; the matching lower bound comes from
finite-geometry constructions.
-/
@[category research solved, AMS 5]
theorem erdos_573.variants.kst :
    (fun n : ℕ ↦ (cycleExtremalNumber ({4} ∪ {k | Odd k ∧ 3 ≤ k}) n : ℝ)) ~[atTop]
      fun n : ℕ ↦ ((n : ℝ) / 2) ^ (3 / 2 : ℝ) := by
  sorry

end Erdos573
