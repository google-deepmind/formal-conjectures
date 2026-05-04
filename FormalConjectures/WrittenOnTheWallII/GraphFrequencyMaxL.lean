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
# Written on the Wall II - Conjecture 209

**Verbatim statement (WOWII #209, status O):**
> If G is a simple connected graph with n > 1 such that
>   (1/6) * [1 + 2 * |E(Ḡ)|]  ≤  frequency of λ_max(G),
> then G has a Hamiltonian path.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj209

Here `λ_max(G)` is interpreted as `max_v l(v)` (the maximum over vertices of
the independence number of the open neighbourhood, the standard reading of
the Greek `λ` across the WOWII conjectures), and `frequency of λ_max(G)` is
the number of vertices `v` that achieve this maximum. `|E(Ḡ)|` is the
edge count of the complement of `G`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphFrequencyMaxL

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The maximum value of `indepNeighborsCard G v` over all vertices `v`. -/
noncomputable def maxLValue (G : SimpleGraph α) : ℕ :=
  Finset.univ.sup (indepNeighborsCard G)

/-- The number of vertices `v` that achieve the maximum value of
`indepNeighborsCard G v`. This is the "frequency of `λ_max(G)`". -/
noncomputable def frequencyMaxL (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter (fun v => indepNeighborsCard G v = maxLValue G)).card

/--
WOWII [Conjecture 209](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj209)
(status O):

If `G` is a simple connected graph on `n > 1` vertices and
`(1/6) · (1 + 2 · |E(Gᶜ)|) ≤ frequencyMaxL G`,
then `G` has a Hamiltonian path.
-/
@[category research open, AMS 5]
theorem conjecture209 (G : SimpleGraph α)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (hn : 1 < Fintype.card α)
    (h : G.Connected)
    (hbound : (1 : ℝ) / 6 * (1 + 2 * (Gᶜ.edgeFinset.card : ℝ)) ≤ frequencyMaxL G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- `frequencyMaxL` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ frequencyMaxL G := Nat.zero_le _

/-- `maxLValue` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ maxLValue G := Nat.zero_le _

end WrittenOnTheWallII.GraphFrequencyMaxL
