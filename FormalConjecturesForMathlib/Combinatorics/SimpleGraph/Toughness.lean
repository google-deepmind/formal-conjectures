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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Toughness

This file defines `SimpleGraph.numComponents` (components after deleting a
vertex set) and `SimpleGraph.toughness` (Chvátal's toughness).
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- Number of connected components of the induced subgraph of `G` on the set
of vertices NOT in `S`.  We count equivalence classes of `Reachable` restricted
to `Sᶜ`. -/
noncomputable def numComponents (G : SimpleGraph α) (S : Finset α) : ℕ :=
  Fintype.card (ConnectedComponent (G.induce (↑Sᶜ : Set α)))

open Classical in
/-- The **toughness** `τ(G)` of a simple graph `G`.

For each nonempty proper vertex set `S` such that `G - S` is disconnected,
we form the ratio `|S| / c(G - S)`.  The toughness is the infimum of these
ratios.  If no such `S` exists (e.g., `G` is complete or has ≤ 1 vertex),
the toughness is defined as `Fintype.card α - 1`, matching the convention
that `Kₙ` has toughness `+∞`.

Note: `numComponents G S = 1` iff `G - S` is connected; we require strictly
more than one component (i.e. `G - S` is disconnected). -/
noncomputable def toughness (G : SimpleGraph α) : ℝ :=
  let separators : Finset (Finset α) :=
    Finset.univ.powerset.filter (fun S =>
      S.Nonempty ∧ S ≠ Finset.univ ∧ 2 ≤ numComponents G S)
  if h : separators.Nonempty then
    separators.inf' h (fun S => (S.card : ℝ) / (numComponents G S : ℝ))
  else
    (Fintype.card α - 1 : ℝ)

end SimpleGraph
