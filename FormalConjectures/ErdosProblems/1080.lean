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

/-!
# Erdős Problem 1080 — Bipartitions of size ⌊n^(2/3)⌋ and 6-cycles

-- [category research open]
-- [AMS 05]
-- tags: graph theory, cycles
-/

import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Real.Basic

open Classical
noncomputable section

namespace Erdos1080

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Minimal bipartition predicate with explicit parts `U, W`. -/
structure IsBipartition (G : SimpleGraph V) (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  cover    : U ∪ W = (Finset.univ : Finset V)
  no_edges_in_U :
    ∀ {x y}, x ∈ U → y ∈ U → ¬ G.Adj x y
  no_edges_in_W :
    ∀ {x y}, x ∈ W → y ∈ W → ¬ G.Adj x y

/-- `G` contains a 6-cycle. -/
def HasC6 (G : SimpleGraph V) : Prop :=
  ∃ (v : Fin 6 → V),
    (∀ i j, i ≠ j → v i ≠ v j) ∧
    (∀ i : Fin 6,
      let j : Fin 6 :=
        ⟨(i.1 + 1) % 6, by decide⟩
      G.Adj (v i) (v j))

/-- Target bipartition size: `⌊n^(2/3)⌋`. -/
def partSize (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (2 / 3 : ℝ))

/-- Formal packaging of the conjecture statement. -/
def Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (U W : Finset V),
        IsBipartition G U W ∧
        U.card = partSize (Fintype.card V) ∧
        ((Nat.ceil (c * (Fintype.card V : ℝ)) : ℕ)
            ≤ G.edgeFinset.card → HasC6 G)

/--
Erdős Problem 1080 in the `problem ↔ answer` format used in the repository.
-/
theorem erdos_1080 :
    Statement ↔ answer (sorry) :=
by
  sorry

end Erdos1080
