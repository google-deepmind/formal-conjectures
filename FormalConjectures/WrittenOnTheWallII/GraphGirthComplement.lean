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

import FormalConjecturesUtil

/-!
# Girth of the Complement Graph

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition

The **complement girth** `Gᶜ.girth` of a graph `G` is the girth of the
complement graph `Gᶜ`, i.e., the length of a shortest cycle in `Gᶜ`.  By the
Mathlib convention, `SimpleGraph.girth Gᶜ = 0` when `Gᶜ` is acyclic (a forest
or edgeless graph).

## Conjectures

1. (Test case) The complement of `K₃` (complete graph on 3 vertices) is the
   empty graph (no edges), which is acyclic, so `(K₃)ᶜ.girth = 0`.

2. (Open) For any simple graph `G`, either `G` contains a triangle or
   `G.indepNum ≤ Gᶜ.girth`.  Informally, if `G` is triangle-free then
   its complement `Gᶜ` is "sparse enough" that the girth of `Gᶜ` is a valid
   upper bound for the independence number of `G`.
-/

namespace WrittenOnTheWallII.GraphGirthComplement

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
**Test-case fact**: The complement of `K_n` (the complete graph on `n` vertices)
is the empty graph (no edges).  An edgeless graph has no cycles, so its girth is 0
by the Mathlib convention.  In particular, `(⊤ : SimpleGraph (Fin n))ᶜ.girth = 0`.
-/
@[category research solved, AMS 5]
theorem girth_compl_completeGraph (n : ℕ) :
    (⊤ : SimpleGraph (Fin n))ᶜ.girth = 0 := by
  simp [compl_top]

/--
**WOWII-style open conjecture**: For any simple connected graph `G`,
either `G` contains a triangle (a 3-clique) or `G.indepNum ≤ Gᶜ.girth`.

Informally: if `G` has no triangle then the complement `Gᶜ` must be relatively
dense (many edges), which tends to create short cycles and thus a small
`Gᶜ.girth`.  Meanwhile, the independence number of a triangle-free graph
can be large.  The conjecture asserts that these two quantities are in balance
unless a triangle is present.
-/
@[category research open, AMS 5]
theorem indepNum_le_girthComplement_or_triangle (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (∃ v w x : α, G.Adj v w ∧ G.Adj w x ∧ G.Adj v x) ∨
    G.indepNum ≤ Gᶜ.girth := by
  sorry

-- Sanity checks

/-- The complement of the 6-cycle `C₆` is the graph `2K₃` (two disjoint triangles).
Its girth is 3, so `(C₆)ᶜ.girth = 3`. -/
@[category test, AMS 5]
example : (cycleGraph 6)ᶜ.girth = 3 := by
  sorry

/-- The complement girth is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ Gᶜ.girth :=
  Nat.zero_le _

/-- For the path `P₃` (0–1–2), the complement has the single edge `{0, 2}`, which
is acyclic, so `(P₃)ᶜ.girth = 0`. -/
@[category test, AMS 5]
example : (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3))ᶜ.girth = 0 := by
  sorry

end WrittenOnTheWallII.GraphGirthComplement
