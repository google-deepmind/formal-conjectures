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
# Written on the Wall II - Conjecture 101

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **$\alpha$-core** of a graph $G$, written `alphaCore G`, is the set of vertices
$v$ such that removing $v$ strictly decreases the independence number:
$$\mathrm{alphaCore}(G) = \{v \mid \alpha(G - v) < \alpha(G)\}$$
where $G - v$ is the subgraph of $G$ induced on $V(G) \setminus \{v\}$.

These vertices are also called "critical vertices for independence."
-/

namespace WrittenOnTheWallII.GraphConjecture101

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The independence number of the subgraph induced on $V \setminus \{v\}$
(i.e., the graph $G - v$). -/
noncomputable def indepNumDeleteVertex (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (Set.univ \ {v})).indepNum

/-- The $\alpha$-core of $G$: the set of vertices whose removal strictly decreases the
independence number. A vertex $v$ is in the $\alpha$-core if $\alpha(G - v) < \alpha(G)$. -/
noncomputable def alphaCore (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => indepNumDeleteVertex G v < G.indepNum)

/--
WOWII [Conjecture 101](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\alpha(G) \le \lfloor (n + |\mathrm{alphaCore}(G)|) / 2 \rfloor$
where $\alpha(G) = G.\mathrm{indepNum}$ is the independence number, $n$ is the
number of vertices, and $\mathrm{alphaCore}(G)$ is the set of vertices whose
removal decreases the independence number.

This is a theorem known to follow from inclusion-exclusion principles.
-/
@[category research solved, AMS 5]
theorem conjecture101 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2 := by
  sorry

-- Sanity checks

/-- The $\alpha$-core has cardinality at most $n$ (the number of vertices). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : (alphaCore G).card ≤ 3 := by
  apply Finset.card_le_univ

/-- The $\alpha$-core is always a subset of all vertices. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : alphaCore G ⊆ Finset.univ :=
  Finset.filter_subset _ _

/-- If a vertex $v$ is NOT in the $\alpha$-core, then removing $v$ does not decrease $\alpha$. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3)
    (hv : v ∉ alphaCore G) :
    G.indepNum ≤ indepNumDeleteVertex G v := by
  unfold alphaCore at hv
  simp [Finset.mem_filter] at hv
  exact hv

/-- If a vertex $v$ IS in the $\alpha$-core, then removing $v$ strictly decreases $\alpha$. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3)
    (hv : v ∈ alphaCore G) :
    indepNumDeleteVertex G v < G.indepNum := by
  unfold alphaCore at hv
  exact (Finset.mem_filter.mp hv).2

end WrittenOnTheWallII.GraphConjecture101
