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
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# Even-distance vertex count

This file defines `SimpleGraph.distEven`, the number of vertices at even
distance from a given vertex. This is DeLaVina's `dist_even(v)` invariant
appearing in several WOWII conjectures (e.g. WOWII #24, #25, #63, #85, #96,
#189). Distance 0 is even, so `v` itself is always counted —
`1 ≤ distEven G v` for any `v`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α]

/-- `distEven G v` counts the number of vertices at even distance from `v` in `G`.
Distance 0 (the vertex itself) is even, so `distEven G v ≥ 1`. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Even (G.dist v w))).card

end SimpleGraph
