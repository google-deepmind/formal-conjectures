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
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# Odd-distance vertex count

This file defines `SimpleGraph.distOdd`, the number of vertices at odd
distance from a given vertex. This is DeLaVina's `dist_odd(v)` invariant from
the WOWII conjecture collection; it is the complementary count to
`dist_even(v)` (the two always sum to the number of vertices).
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `distOdd G v` counts the number of vertices at odd distance from `v` in `G`.
Note: since `G.dist v v = 0` is even, `v` itself is never counted here. -/
noncomputable def distOdd (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Odd (G.dist v w))).card

end SimpleGraph
