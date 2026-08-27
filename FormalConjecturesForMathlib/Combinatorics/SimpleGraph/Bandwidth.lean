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
# Bandwidth

This file defines `SimpleGraph.bandwidth`, the minimum over all linear
arrangements of the maximum edge label-difference.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **bandwidth** of `G` is the minimum, over all bijections
`f : α ≃ Fin (Fintype.card α)`, of the maximum edge label-difference.

`sInf` over a set of natural numbers returns 0 when the set is empty;
here the set is always nonempty because `Fin (Fintype.card α)` is in bijection
with `α` (via `Fintype.equivFin`), so the bandwidth is well-defined. -/
noncomputable def bandwidth (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ f : α ≃ Fin (Fintype.card α),
    ∀ u v : α, G.Adj u v → (Int.natAbs ((f u : ℤ) - (f v : ℤ))) ≤ k}

end SimpleGraph
