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

public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-!
# Metric dimension

This file defines `SimpleGraph.metricDimension`, the minimum size of a
resolving set of vertices.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `R` of vertices **resolves** the graph `G` if, for every pair of
distinct vertices `u ≠ v`, some `r ∈ R` has `dist(u, r) ≠ dist(v, r)`. -/
def IsResolvingSet (G : SimpleGraph α) (R : Finset α) : Prop :=
  ∀ u v : α, u ≠ v → ∃ r ∈ R, G.dist u r ≠ G.dist v r

/-- The **metric dimension** of `G`: the minimum size of a resolving set.
Returns 0 when no resolving set exists (e.g., `G` has ≤ 1 vertex), which is
consistent since `sInf ∅ = 0` for `ℕ`. -/
noncomputable def metricDimension (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ R : Finset α, R.card = k ∧ IsResolvingSet G R}

end SimpleGraph
