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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The cycle rank of `G` (or cyclomatic number) is the minimum number of edges
    that must be removed to eliminate all cycles. -/
noncomputable def cycleRank (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card + Fintype.card G.ConnectedComponent - Fintype.card α

end SimpleGraph
