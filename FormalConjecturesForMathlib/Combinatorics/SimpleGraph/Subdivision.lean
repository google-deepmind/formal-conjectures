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

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Complete graph subdivisions
-/

@[expose] public section

namespace SimpleGraph

/-- The interior vertices of a walk from `u` to `v`: its support with the endpoints removed. -/
def walkInterior {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- `G` contains a subdivision of `K_r`: there are `r` distinct branch vertices and, for each
pair of them, a path in `G` joining them, such that the interiors of these paths are pairwise
disjoint and avoid the branch vertices. -/
def ContainsSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ (b : Fin r ↪ V) (p : ∀ e : {e : Fin r × Fin r // e.1 < e.2}, G.Walk (b e.1.1) (b e.1.2)),
    (∀ e, (p e).IsPath) ∧ (∀ e, Disjoint (walkInterior (p e)) (Set.range b)) ∧
      Pairwise fun e f ↦ Disjoint (walkInterior (p e)) (walkInterior (p f))

end SimpleGraph
