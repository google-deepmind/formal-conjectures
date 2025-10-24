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
-/

namespace Erdos1080

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Minimal bipartition predicate with explicit parts `U, W`:
disjoint, cover all vertices, and no edges inside each part. -/
structure IsBipartition (G : SimpleGraph V) (U W : Finset V) : Prop :=
(disjoint : Disjoint U W)
(cover   : U ∪ W = (univ : Finset V))
(no_edges_in_U : ∀ ⦃x y⦄, x ∈ U → y ∈ U → ¬ G.Adj x y)
(no_edges_in_W : ∀ ⦃x y⦄, x ∈ W → y ∈ W → ¬ G.Adj x y)

/-- `G` contains a 6-cycle: six distinct vertices with cyclic adjacencies. -/
def HasC6 (G : SimpleGraph V) : Prop :=
  ∃ (v : Fin 6 → V),
    (∀ i j, i ≠ j → v i ≠ v j) ∧
    (∀ i : Fin 6, G.Adj (v i) (v ⟨(i.1 + 1) % 6, by
      have : (i.1 + 1) % 6 < 6 := Nat.mod_lt _ (by decide)
      exact this⟩))

/-- Size of the designated part: `⌊ n^(2/3) ⌋`. -/
def partSize (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ (2 / 3 : ℝ))

/-!
## Conjecture (formal shell)

There exists a universal `c > 0` such that for every finite simple graph `G` on `n` vertices,
if `G` is bipartite with one part of size `⌊ n^(2/3) ⌋` and `|E(G)| ≥ c n`, then `G` has a `C₆`.
-/
@[category research open, AMS 05, tags "graph theory, cycles"]
theorem erdos_1080_statement :
  ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (U W : Finset V),
        IsBipartition G U W ∧
        U.card = partSize (Fintype.card V) ∧
        (Nat.ceil (c * (Fintype.card V)) : ℕ) ≤ G.edgeFinset.card →
        HasC6 G := ↔ answer(sorry) := by
  sorry

end Erdos1080
