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
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Achromatic number

This file defines `SimpleGraph.achromaticNumber`, the maximum number of colors
in a complete proper coloring.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A **complete proper `k`-coloring**: a proper vertex coloring `c : V → Fin k`
such that every pair of distinct color classes is connected by at least one edge. -/
def IsCompleteProperColoring (G : SimpleGraph α) {k : ℕ} (c : α → Fin k) : Prop :=
  (∀ u v : α, G.Adj u v → c u ≠ c v) ∧
  (∀ i j : Fin k, i ≠ j → ∃ u v : α, c u = i ∧ c v = j ∧ G.Adj u v)

/-- The **achromatic number** `ψ(G)`: the maximum number of colors in a
complete proper coloring. -/
noncomputable def achromaticNumber (G : SimpleGraph α) : ℕ :=
  sSup {k | ∃ c : α → Fin k, IsCompleteProperColoring G c}

end SimpleGraph
