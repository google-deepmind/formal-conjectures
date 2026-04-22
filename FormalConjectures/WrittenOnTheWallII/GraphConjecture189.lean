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
# Written on the Wall II - Conjecture 189

**Verbatim statement (WOWII #189, status O):**
> If G is a simple connected graph with n > 1 such that maximum { dist_even(v) : dist_even(v) is the number of vertices at even distance from v } ≤ 1 + σ(G), then G has a Hamiltonian path.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj189


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture189

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `distEven G v` counts the number of vertices at even distance from `v` in `G`. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Even (G.dist v w))).card

/-- The 2-domination number of `G`: the minimum size of a set `S` such that every
vertex outside `S` has at least 2 neighbours in `S`.
This is the interpretation of `σ(G)` appearing in Conjecture 189.
-- TODO: verify this matches DeLaVina's original notation for σ(G). -/
noncomputable def twoDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf { n | ∃ S : Finset α, S.card = n ∧
    ∀ v ∉ S, 2 ≤ (S.filter (fun w => G.Adj v w)).card }

/--
WOWII [Conjecture 189](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `max_v distEven(v) ≤ 1 + σ(G)`,
then `G` has a Hamiltonian path.
Here `distEven(v)` is the number of vertices at even distance from `v` and
`σ(G) = twoDominationNumber G` is the 2-domination number of `G`.

Note: The precise meaning of σ(G) in DeLaVina's original is uncertain; we use the
2-domination number as the most natural interpretation.
-/
@[category research open, AMS 5]
theorem conjecture189 (G : SimpleGraph α) (h : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + twoDominationNumber G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- The 2-domination number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ twoDominationNumber G := Nat.zero_le _

/-- `distEven G v` is positive for any vertex `v`. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 < distEven G v := by
  unfold distEven
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, by simp [SimpleGraph.dist_self]⟩⟩⟩

end WrittenOnTheWallII.GraphConjecture189
