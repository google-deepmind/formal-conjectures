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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Isoperimetric number (Cheeger constant)

This file defines `SimpleGraph.edgeBoundaryCard` and
`SimpleGraph.isoperimetricNumber`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- The **edge boundary cardinality** `|∂(S)|`: the number of edges of `G` with
exactly one endpoint in `S`. -/
noncomputable def edgeBoundaryCard (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    Sym2.lift ⟨fun u v => (u ∈ S) ≠ (v ∈ S), fun u v => by simp [Iff.comm]⟩ e)).card

open Classical in
/-- The **isoperimetric number** (Cheeger constant) `h(G)`:
  `h(G) = inf { |∂(S)| / |S| | S ⊆ V, S ≠ ∅, 2·|S| ≤ n }`.

We take the infimum over nonempty vertex subsets `S` satisfying `2 · |S| ≤ n`
of the ratio `|∂(S)| / |S|` as a real number. -/
noncomputable def isoperimetricNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {r | ∃ S : Finset α, S.Nonempty ∧ 2 * S.card ≤ Fintype.card α ∧
    r = (edgeBoundaryCard G S : ℝ) / (S.card : ℝ)}

end SimpleGraph
