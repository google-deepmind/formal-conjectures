/-
Copyright 2025 The Formal Conjectures Authors.

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

**Verbatim statement (WOWII #145, status O):**
> If G is a simple connected graph, then tree(G) ≥ 2*ecc(B)/λ_min(Ḡ)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj145

The WOWII HTML uses `λ_min(Ḡ)` (the bar denotes graph complement); the
extracted JSON in our private repo previously dropped the overline. The
formal statement below uses the local-independence minimum of `Gᶜ`.


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **local independence minimum** `lMin(G)` is:
  `lMin(G) = min_{v ∈ V(G)} l(v)`
where `l(v) = indepNeighborsCard(G, v)` is the independence number of the neighbourhood of `v`.
This is the minimum over all vertices of the local independence number.

The **boundary vertices** `B(G)` of a connected graph are the vertices `v` such that
the eccentricity of `v` equals the diameter of `G`.

The **eccentricity of a set** `ecc(S)` = max over all vertices `u ∉ S` of the minimum
distance from `u` to any vertex in `S`.  In the conjecture below, `ecc(B)` is the
eccentricity of the boundary set.

**Note on Conjecture 145:** The statement is
  `tree(G) ≥ 2 * ecc(B) / λ_min(Ḡ)`
where `tree(G)` is `largestInducedTreeSize G`, `ecc(B)` is the eccentricity of the
boundary vertices, and `λ_min(Ḡ)` is the local independence minimum of the complement `Ḡ`.
-/

namespace WrittenOnTheWallII.GraphConjecture145

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `localIndependenceMin G` is the minimum over all vertices of the local independence
number `indepNeighborsCard G v`. This equals `lMin` from DeLaVina's notation. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

/-- The set of boundary vertices: vertices whose eccentricity equals the diameter. -/
noncomputable def boundaryVertices (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => eccentricity G v = maxEccentricity G)

/-- The eccentricity of a set `S` relative to `G`: the maximum over all vertices `u`
of the minimum distance from `u` to any vertex in `S`.
If `S` is empty, defined to be 0. -/
noncomputable def eccSet (G : SimpleGraph α) (S : Finset α) : ℕ :=
  if h : S.Nonempty then
    (Finset.univ.image (fun u => (S.image (G.dist u)).min' (Finset.Nonempty.image h _))).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
  else 0

/--
WOWII [Conjecture 145](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`tree(G) ≥ 2 * ecc(B) / λ_min(Ḡ)`
where `tree(G)` is the number of vertices in a largest induced subtree,
`ecc(B)` is the eccentricity of the boundary vertices, and
`λ_min(Ḡ)` is the minimum local independence number of the complement graph.

We state the inequality in the form `tree(G) * lMin(Ḡ) ≥ 2 * ecc(B)` to avoid division.
-/
@[category research open, AMS 5]
theorem conjecture145 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (boundaryVertices G) ≤
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
example (G : SimpleGraph (Fin 3)) : 0 ≤ eccSet G (boundaryVertices G) := Nat.zero_le _

/-- `boundaryVertices` is a subset of all vertices. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : boundaryVertices G ⊆ Finset.univ := by
  intro v _; exact Finset.mem_univ v

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
