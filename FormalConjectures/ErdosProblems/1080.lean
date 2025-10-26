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
# Erdős Problem 1080 — Bipartitions of size ⌊n^(2/3)⌋ and 6-cycles

*Reference:* https://www.erdosproblems.com/1080

Let `G` be a bipartite simple graph on `n` vertices such that one part has size `⌊ n^(2/3) ⌋`.
Is there a constant `c > 0` such that if `|E(G)| ≥ c n`, then `G` contains a 6-cycle `C₆`?

**Status:** open.

Choice: *I plan on working on this conjecture.*

-- [category research open]
-- [AMS 05C38]
-- tags: graph theory, cycles
-/

open Classical
noncomputable section

namespace Erdos1080

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `edgeSet` is finite since it is a subtype of `Sym2 V`, which is finite for finite `V`. -/
instance (G : SimpleGraph V) : Fintype G.edgeSet := by
  classical
  exact Fintype.ofFinite (G.edgeSet)

/-- Minimal bipartition predicate with explicit parts `U, W`. -/
structure IsBipartition (G : SimpleGraph V) (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  cover   : U ∪ W = (univ : Finset V)
  no_edges_in_U : ∀ ⦃x y⦄, x ∈ U → y ∈ U → ¬ G.Adj x y
  no_edges_in_W : ∀ ⦃x y⦄, x ∈ W → y ∈ W → ¬ G.Adj x y

/-- `G` contains a 6-cycle: six distinct vertices with cyclic adjacencies. -/
def HasC6 (G : SimpleGraph V) : Prop :=
  ∃ (v : Fin 6 → V),
    (∀ i j, i ≠ j → v i ≠ v j) ∧
    (∀ i : Fin 6,
      G.Adj (v i)
        (v ⟨(i.1 + 1) % 6,
            by
              have : 0 < 6 := by decide
              exact Nat.mod_lt _ this⟩))

/-- Size of the designated part: `⌊ n^(2/3) ⌋`. -/
def partSize (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (2 / 3 : ℝ))

/-- Erdős Problem 1080 (conjecture shell). -/
theorem erdos_1080_statement :
  ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (U W : Finset V),
        IsBipartition G U W ∧
        U.card = partSize (Fintype.card V) ∧
        ((Nat.ceil (c * (Fintype.card V : ℝ)) : ℕ) ≤ G.edgeFinset.card → HasC6 G) := by
  sorry

end Erdos1080
