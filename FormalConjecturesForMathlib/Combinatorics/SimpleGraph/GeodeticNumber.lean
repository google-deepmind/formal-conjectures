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
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

/-!
# Geodetic number

This file defines `SimpleGraph.geodeticNumber`, the minimum size of a set of
vertices whose geodesics cover the whole graph.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `S` is a **geodetic set** of `G` if every vertex `v` lies on a
shortest `u`-`w` path for some `u, w ∈ S`.

A walk `p` is a shortest path from `u` to `w` if it is a path and its length
equals `G.dist u w`. -/
def IsGeodeticSet (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ v : α, ∃ u ∈ S, ∃ w ∈ S,
    ∃ p : G.Walk u w, p.IsPath ∧ p.length = G.dist u w ∧ v ∈ p.support

/-- The **geodetic number** of `G`: the minimum size of a geodetic set.
Returns 0 when no geodetic set exists; for any connected graph with ≥ 2 vertices
the value is at least 2. -/
noncomputable def geodeticNumber (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ S : Finset α, S.card = k ∧ IsGeodeticSet G S}

end SimpleGraph
