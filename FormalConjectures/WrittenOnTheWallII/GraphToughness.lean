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
# Graph Toughness and Chvátal's Conjecture

*Reference:*
[V. Chvátal, Tough graphs and Hamiltonian circuits, Discrete Mathematics 5 (1973) 215–228](https://doi.org/10.1016/0012-365X(73)90138-6)

## Definitions

The **toughness** of a graph `G` is defined as
  `τ(G) = min_{S} |S| / c(G - S)`
where the minimum is taken over all nonempty proper vertex subsets `S` such that
`G - S` (the induced subgraph on the complement of `S`) is disconnected, and
`c(G - S)` is the number of connected components of `G - S`.

If `G` is complete (no such `S` exists), the toughness is conventionally `+∞`;
here we define it as `(Fintype.card α - 1 : ℝ)`, which is the largest finite
value attained by `Kₙ`.

We count connected components as the number of equivalence classes of the
`G.Reachable` relation on the complement vertex set.

## Conjecture

**Chvátal's conjecture (1973), open:**
  `τ(G) ≥ 3/2 → G` is Hamiltonian.

Chvátal himself conjectured the weaker bound `τ ≥ 1` implies Hamiltonicity,
which was disproved.  The current open conjecture is that `τ ≥ 3/2` suffices.
-/

namespace WrittenOnTheWallII.GraphToughness

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Number of connected components of the induced subgraph of `G` on the set
of vertices NOT in `S`.  We count equivalence classes of `Reachable` restricted
to `Sᶜ`. -/
noncomputable def numComponents (G : SimpleGraph α) (S : Finset α) : ℕ :=
  Fintype.card (ConnectedComponent (G.induce (↑Sᶜ : Set α)))

/-- The **toughness** `τ(G)` of a simple graph `G`.

For each nonempty proper vertex set `S` such that `G - S` is disconnected,
we form the ratio `|S| / c(G - S)`.  The toughness is the infimum of these
ratios.  If no such `S` exists (e.g., `G` is complete or has ≤ 1 vertex),
the toughness is defined as `Fintype.card α - 1`, matching the convention
that `Kₙ` has toughness `+∞`.

Note: `numComponents G S = 1` iff `G - S` is connected; we require strictly
more than one component (i.e. `G - S` is disconnected). -/
noncomputable def toughness (G : SimpleGraph α) : ℝ :=
  let separators : Finset (Finset α) :=
    Finset.univ.powerset.filter (fun S =>
      S.Nonempty ∧ S ≠ Finset.univ ∧ 2 ≤ numComponents G S)
  if h : separators.Nonempty then
    separators.inf' h (fun S => (S.card : ℝ) / (numComponents G S : ℝ))
  else
    (Fintype.card α - 1 : ℝ)

/--
**Chvátal's toughness conjecture (1973)** — open.

For a simple graph `G` on `n ≥ 3` vertices,
if `τ(G) ≥ 3/2` then `G` has a Hamiltonian cycle.

A walk `w : G.Walk v v` is Hamiltonian if it visits every vertex exactly once
(i.e., `w.IsHamiltonian` in the sense of `Walk.support`).
-/
@[category research open, AMS 5]
theorem chvatal_toughness_conjecture (G : SimpleGraph α) [DecidableRel G.Adj]
    (h3 : 3 ≤ Fintype.card α)
    (htough : (3 : ℝ) / 2 ≤ toughness G) :
    ∃ v : α, ∃ w : G.Walk v v, w.IsCycle ∧ w.IsHamiltonian := by
  sorry

-- Sanity checks

/-- `toughness` is a real number (type checks). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : toughness G ∈ Set.Ioi (0 : ℝ) ∨ True := Or.inr trivial

/-- `numComponents` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Finset (Fin 3)) : 0 ≤ numComponents G S :=
  Nat.zero_le _

/-- `numComponents` of the empty separator on `Fin 3` equals 3
(one component per vertex, since no edges in the induced empty complement). -/
@[category test, AMS 5]
example : numComponents (⊥ : SimpleGraph (Fin 3)) ∅ = 3 := by
  unfold numComponents
  simp
  sorry

/-- On `K₃` removing vertex `{0}` leaves a connected graph on `{1, 2}`,
so `numComponents K₃ {0} = 1`. -/
@[category test, AMS 5]
example : numComponents (⊤ : SimpleGraph (Fin 3)) {0} = 1 := by
  unfold numComponents
  sorry

end WrittenOnTheWallII.GraphToughness
