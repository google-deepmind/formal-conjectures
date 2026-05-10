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
# Written on the Wall II - Conjecture 314

**Verbatim statement (WOWII #314, status O):**
> Let G is a simple connected graph with n > 1. If G is triangle-free and path number ≤ 4, then G is well total dominated.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj314


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `S` is a total dominating set of `G` if every vertex has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

/-- A total dominating set `S` is minimal if no proper subset of `S` is also a
total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

/-- A graph `G` is well totally dominated if every minimal total dominating set
has the same cardinality. -/
def isWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

/-- The size of a largest induced path of `G`, as a natural number.

A subset `s ⊆ V(G)` is an *induced path* when the induced subgraph
`G.induce s` is a tree in which every vertex has degree at most `2`
(equivalently: a tree that is itself a path graph). We define
`largestInducedPathSize G` as the supremum of `s.card` over all such subsets.

**Disambiguation.** This is *not* the upstream `SimpleGraph.path` invariant
from `FormalConjecturesForMathlib/.../Invariants.lean`, which is the floor of
the average distance — that one is the wrong tool for WOWII Conjecture 314,
where `path(G)` denotes the **size of a largest induced path**.

TODO: it would probably be clearer to rename the upstream `SimpleGraph.path`
invariant to something like `pathBound` / `floorAvgDist` to avoid this naming
collision; that rename lives outside the scope of this PR. -/
noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

/--
WOWII [Conjecture 314](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj314)
(status O):

For every finite simple connected graph `G` with `n > 1` vertices,
if `G` is triangle-free and `path(G) ≤ 4`, then `G` is well totally dominated.

Here `path(G) = largestInducedPathSize G` is the **size of a largest induced
path** in `G`, defined locally above.

**Disambiguation.** Earlier revisions of this file used the upstream
`SimpleGraph.path` invariant
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/GraphConjectures/Invariants.lean`),
but that is the *floor of the average distance*, not the size of a largest
induced path — a different quantity that makes Conjecture 314 vacuous in many
cases. (Cf. Paul-Lez review on PR #3820.)
-/
@[category research open, AMS 5]
theorem conjecture314 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    isWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- The complete graph `K₃` has a triangle. -/
@[category test, AMS 5]
example : ∃ a b c : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj a b ∧
    (⊤ : SimpleGraph (Fin 3)).Adj b c ∧ (⊤ : SimpleGraph (Fin 3)).Adj c a := by
  exact ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- `largestInducedPathSize G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    0 ≤ largestInducedPathSize G := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture314
