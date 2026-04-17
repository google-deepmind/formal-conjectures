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
# Written on the Wall II - Conjecture 199

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture199

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/-- The vertex connectivity `κ(G)`: the minimum number of vertices whose removal
disconnects the graph (or `n - 1` when the graph is complete).
Vertex connectivity is not yet in Mathlib; we define it here as the minimum size of
a vertex separator, where removing `S` leaves the induced subgraph on `Sᶜ` disconnected.
-- TODO: replace with a Mathlib definition when one becomes available. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ :=
  if Fintype.card α ≤ 1 then 0
  else sInf { k | ∃ S : Finset α, S.card = k ∧
    (¬(G.induce (↑Sᶜ : Set α)).Connected ∨ S.card = Fintype.card α - 1) }

/--
WOWII [Conjecture 199](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `tree(G) - 2 ≤ κ(G)`, then `G` has a Hamiltonian path.
Here `tree(G)` is the number of vertices in a largest induced tree and
`κ(G) = vertexConnectivity G` is the vertex connectivity of `G`.
-/
@[category research open, AMS 5]
theorem conjecture199 (G : SimpleGraph α) (h : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The vertex connectivity is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ vertexConnectivity G := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture199
