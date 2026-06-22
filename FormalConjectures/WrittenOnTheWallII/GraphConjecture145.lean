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
# Written on the Wall II - Conjecture 145

The WOWII HTML uses $\lambda_{\min}(\overline{G})$ (the bar denotes graph complement).
The formal statement below uses the local-independence minimum of $G^c$.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **local independence minimum** $\mathrm{lMin}(G)$ is:
$$\mathrm{lMin}(G) = \min_{v \in V(G)} l(v)$$
where $l(v) = \mathrm{indepNeighborsCard}(G, v)$ is the independence number of the
neighbourhood of $v$. This is the minimum over all vertices of the local
independence number.

The **boundary vertices** $B(G)$ of a connected graph are the vertices $v$ such
that the eccentricity of $v$ equals the diameter of $G$.

The **eccentricity of a set** $\mathrm{ecc}(S) = \max_{u \notin S} \min_{w \in S}
\mathrm{dist}(u, w)$. In the conjecture below, $\mathrm{ecc}(B)$ is the
eccentricity of the boundary set.

**Conjecture 145:** $\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) /
\lambda_{\min}(\overline{G})$ where $\mathrm{tree}(G)$ is `largestInducedTreeSize G`,
$\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices, and
$\lambda_{\min}(\overline{G})$ is the local independence minimum of the complement
$\overline{G}$.
-/

namespace WrittenOnTheWallII.GraphConjecture145

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `localIndependenceMin G` is the minimum over all vertices of the local independence
number `indepNeighborsCard G v`. This equals $\mathrm{lMin}$ from DeLaVina's notation. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

/--
WOWII [Conjecture 145](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) / \lambda_{\min}(\overline{G})$
where $\mathrm{tree}(G)$ is the number of vertices in a largest induced subtree,
$\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices (`eccSet` and
`boundaryVertices`), and $\lambda_{\min}(\overline{G})$ is the minimum local
independence number of the complement graph.

We state the inequality in the form
$\mathrm{tree}(G) \cdot \mathrm{lMin}(\overline{G}) \ge 2 \cdot \mathrm{ecc}(B)$
to avoid division.
-/
@[category research open, AMS 5]
theorem conjecture145 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  sorry

-- Sanity checks

/-- `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- `localIndependenceMin` is nonneg (it is a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ localIndependenceMin G := Nat.zero_le _

/-- For any graph on `Fin 3`, `eccSet` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ eccSet G (maxEccentricityVertices G) :=
  Nat.zero_le _

/-- `maxEccentricityVertices` is a subset of all vertices. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : maxEccentricityVertices G ⊆ Set.univ := by
  intro v _; exact Set.mem_univ v

/-- `localIndependenceMin G` is at most `indepNeighborsCard G v` for any vertex `v`.
This follows from the definition of `inf'` as the minimum. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    localIndependenceMin G ≤ indepNeighborsCard G v := by
  unfold localIndependenceMin
  apply Finset.inf'_le
  exact Finset.mem_univ v

/-- `localIndependenceMin G` is a natural number, hence nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ localIndependenceMin G := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture145
