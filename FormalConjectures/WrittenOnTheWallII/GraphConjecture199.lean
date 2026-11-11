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

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 199

**Verbatim statement (WOWII #199, status O):**
> If G is a simple connected graph with n > 1 such that tree(G) - 2 ≤ κ(G), then G has a Hamiltonian path.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj199


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture199

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 199](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `tree(G) - 2 ≤ κ(G)`, then `G` has a Hamiltonian path.
The nontrivial vertex type encodes the source assumption $n > 1$.
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

/-- The empty graph has vertex connectivity zero. -/
@[category test, AMS 5]
theorem vertexConnectivity_empty : vertexConnectivity (⊥ : SimpleGraph (Fin 0)) = 0 := by
  simp

/-- A single vertex has vertex connectivity zero. -/
@[category test, AMS 5]
theorem vertexConnectivity_singleton : vertexConnectivity (⊤ : SimpleGraph (Fin 1)) = 0 := by
  simp

/-- Two isolated vertices have vertex connectivity zero. -/
@[category test, AMS 5]
theorem vertexConnectivity_disconnected : vertexConnectivity (⊥ : SimpleGraph (Fin 2)) = 0 := by
  exact vertexConnectivity_eq_zero_of_not_connected _ not_connected_bot

/-- The complete graph on three vertices has vertex connectivity two. -/
@[category test, AMS 5]
theorem vertexConnectivity_complete_three : vertexConnectivity (⊤ : SimpleGraph (Fin 3)) = 2 := by
  classical
  rw [vertexConnectivity, if_neg (by decide)]
  apply le_antisymm
  · exact csInf_le' ⟨{0, 1}, by decide, Or.inr (by decide)⟩
  · refine le_csInf ?_ ?_
    · exact ⟨2, {0, 1}, by decide, Or.inr (by decide)⟩
    · rintro k ⟨S, rfl, hS⟩
      exact (by decide +kernel : ∀ S : Finset (Fin 3),
        (¬((⊤ : SimpleGraph (Fin 3)).induce ((S : Set (Fin 3))ᶜ)).Connected ∨
          S.card = Fintype.card (Fin 3) - 1) → 2 ≤ S.card) S hS

end WrittenOnTheWallII.GraphConjecture199
