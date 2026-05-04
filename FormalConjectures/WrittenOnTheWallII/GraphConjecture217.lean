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
# Written on the Wall II - Conjecture 217

**Verbatim statement (WOWII #217, status O):**
> If G is a simple connected graph with n > 1 such that L(G) ≤ 4*χ_residue=2(G) + 2, then G has a Hamiltonian path.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Statement

WOWII Conjecture 217:
  *If `G` is a simple connected graph with `n > 1` such that
   `L(G) ≤ 4 · c_{residue=2}(G) + 2`, then `G` has a Hamiltonian path.*

Here:
- `L(G)` is the **leaf number** of `G`: the minimum number of leaves over all
  spanning trees of `G`.
- `c_{residue=2}(G)` is the number of connected components of the
  **residue-2 core** of `G` (the maximal induced subgraph of minimum degree
  at least 2, obtained by iteratively peeling off vertices of degree `< 2`).

## Definitions

The residue-2 core can be characterised non-iteratively as the **union of all
2-core subsets** of `V(G)`. This union is itself a 2-core (a vertex with ≥ 2
neighbours in some `Sᵢ` has ≥ 2 neighbours in their union), so it is the
unique maximal 2-core. We use this union-based definition to avoid the
well-founded recursion that the iterative peeling description would require,
and define `residue2ComponentCount G` as the connected-component count of
the subgraph `G` induces on the residue-2 core.

`leafNumber G` is the minimum leaf count of a spanning subtree of `G` (or `0`
by `sInf`-convention if no spanning subtree exists).
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/- ### 2-core predicate -/

/-- A set `S ⊆ V(G)` is a **2-core** of `G` if every vertex in `S` has at least 2
neighbours within `S`. -/
def Is2Core (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v ∈ S, 2 ≤ (S.filter (fun w => G.Adj v w)).card

/- ### Residue-2 core and component count -/

/-- The **residue-2 core** of `G`: the union of all subsets `S ⊆ V(G)` on
which every vertex has at least 2 neighbours in `S`. This is the unique
maximal 2-core of `G` and equals the fixpoint of iteratively removing
vertices of degree less than 2 (proof of equivalence deferred). -/
noncomputable def residue2Core (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  (Finset.univ.powerset.filter (Is2Core G)).sup id

/-- The number of connected components of the subgraph `G` induces on the
residue-2 core. -/
noncomputable def residue2ComponentCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Nat.card (G.induce (residue2Core G : Set α)).ConnectedComponent

/- ### Leaf number

The **leaf number** `L(G)` is the minimum number of leaves (degree-1 vertices)
over all spanning trees of `G`.  A spanning tree here is an induced subtree on
the full vertex set of `G` under the restriction of `G.Adj`. -/

/-- The number of leaves of the graph `T` (vertices of degree `1`). -/
noncomputable def numLeaves (T : SimpleGraph α) [DecidableRel T.Adj] : ℕ :=
  (Finset.univ.filter (fun v => T.degree v = 1)).card

/-- The **leaf number** of `G`: the minimum number of leaves over all spanning
subtrees of `G`, i.e. subgraphs `T ⊆ G` that are trees and have the same vertex
set as `G`.  If no such tree exists we take the infimum over the empty set,
which is `0` (by convention of `sInf` on `ℕ`). -/
noncomputable def leafNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ T : SimpleGraph α, T ≤ G ∧ T.IsTree ∧
    ∃ _ : DecidableRel T.Adj, numLeaves T = k }

/--
WOWII [Conjecture 217](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is a simple connected graph with `n > 1` and
`L(G) ≤ 4 · c_{residue=2}(G) + 2`,
then `G` has a Hamiltonian path, where `L(G)` is the leaf number of `G`
(minimum leaves over all spanning trees) and `c_{residue=2}(G)` is the
connected-component count of the residue-2 core of `G`.
-/
@[category research open, AMS 5]
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : leafNumber G ≤ 4 * residue2ComponentCount G + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- `residue2ComponentCount` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    0 ≤ residue2ComponentCount G :=
  Nat.zero_le _

/-- `leafNumber` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : 0 ≤ leafNumber G := Nat.zero_le _

/-- The empty set is always a 2-core: the condition is vacuous. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : Is2Core G ∅ :=
  fun _ hv => by simp at hv

end WrittenOnTheWallII.GraphConjecture217
