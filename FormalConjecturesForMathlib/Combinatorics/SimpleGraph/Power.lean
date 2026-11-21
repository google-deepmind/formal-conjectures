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
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

/-!
# Graph powers

This file defines `SimpleGraph.graphPower` (the `k`-th distance power of a
graph) and `SimpleGraph.radiusOfPower`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **k-th power** of a graph `G`: vertices `u` and `v` are adjacent iff
`u ≠ v` and `G.dist u v ≤ k`.  For `k = 0` this gives the empty graph; for `k = 1`
it coincides with `G` on connected components (any walk of length ≤ 1 is an edge). -/
noncomputable def graphPower (G : SimpleGraph α) (k : ℕ) : SimpleGraph α where
  Adj u v := u ≠ v ∧ G.dist u v ≤ k
  symm := ⟨fun _ _ h => ⟨h.1.symm, dist_comm (G := G) ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The radius of the k-th power of `G`, i.e., the minimum eccentricity of
`graphPower G k`. -/
noncomputable def radiusOfPower (G : SimpleGraph α) (k : ℕ) : ℕ :=
  (graphPower G k).radius.toNat

end SimpleGraph
