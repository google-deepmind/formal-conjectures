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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 314

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The size of a largest induced path of $G$, as a natural number.

A subset $s \subseteq V(G)$ is an *induced path* when the induced subgraph
`G.induce s` is a tree in which every vertex has degree at most $2$
(equivalently: a tree that is itself a path graph). We define
`largestInducedPathSize G` as the supremum of `s.card` over all such subsets.

**Disambiguation.** This is *not* the `SimpleGraph.path` invariant, which is the
floor of the average distance — that one is the wrong tool for WOWII Conjecture
314, where $\mathrm{path}(G)$ denotes the **size of a largest induced path**.

TODO: it would probably be clearer to rename the `SimpleGraph.path` invariant to
something like `pathBound` / `floorAvgDist` to avoid this naming collision. -/
noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

/--
WOWII [Conjecture 314](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj314):

For every finite simple connected graph $G$ with $n > 1$ vertices,
if $G$ is triangle-free and $\mathrm{path}(G) \le 4$, then $G$ is well totally
dominated.

Here $\mathrm{path}(G) = \mathrm{largestInducedPathSize}\, G$ is the **size of a
largest induced path** in $G$, defined locally above.

**Disambiguation.** Earlier revisions of this file used the `SimpleGraph.path`
invariant, but that is the *floor of the average distance*, not the size of a
largest induced path — a different quantity that makes Conjecture 314 vacuous
in many cases.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/cf59008ef1cd432bf9803275dcf5d62ab1f094a3/FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean"]
theorem conjecture314 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- The complete graph $K_3$ has a triangle. -/
@[category test, AMS 5]
example : ∃ a b c : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj a b ∧
    (⊤ : SimpleGraph (Fin 3)).Adj b c ∧ (⊤ : SimpleGraph (Fin 3)).Adj c a := by
  exact ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- `largestInducedPathSize G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    0 ≤ largestInducedPathSize G := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture314
