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

import FormalConjecturesUtil

/-!
# Tuza's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Tuza%27s_conjecture)
* [Tu90] Tuza, Zs. (1990). "A conjecture on triangles of graphs." *Graphs Combin.* 6,
  pp. 373--380.
* [Ha99] Haxell, P. E. (1999). "Packing and covering triangles in graphs." *Discrete Math.*
  195, pp. 251--254.
-/

namespace TuzaConjecture

variable {V : Type*}

/-- `C` is a **triangle cover** of `G`: a set of edges of `G` meeting every triangle of `G`.
Removing the edges of `C` from `G` leaves a triangle-free graph. -/
def IsTriangleCover (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  C ⊆ G.edgeSet ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ C, ∀ x ∈ e, x ∈ t

/-- `T` is a **triangle packing** of `G`: a set of pairwise edge-disjoint triangles of `G`.
Two distinct triangles are edge-disjoint exactly when they share at most one vertex. -/
def IsTrianglePacking (G : SimpleGraph V) (T : Set (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → ((t₁ : Set V) ∩ (t₂ : Set V)).ncard ≤ 1

/-- The **triangle covering number** `τ(G)`: the least number of edges meeting every triangle
of `G`. -/
noncomputable def triangleCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard = n}

/-- The **triangle packing number** `ν(G)`: the greatest number of pairwise edge-disjoint
triangles of `G`. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ T : Set (Finset V), IsTrianglePacking G T ∧ T.ncard = n}

/-- The empty set of edges covers all triangles of a triangle-free graph. -/
@[category API, AMS 5]
lemma isTriangleCover_empty (G : SimpleGraph V) (h : G.CliqueFree 3) :
    IsTriangleCover G (∅ : Set (Sym2 V)) := by
  refine ⟨Set.empty_subset _, fun t ht => ?_⟩
  exact absurd ht (h t)

/-- A triangle-free graph has triangle covering number zero. -/
@[category API, AMS 5]
lemma triangleCoverNumber_eq_zero (G : SimpleGraph V) (h : G.CliqueFree 3) :
    triangleCoverNumber G = 0 :=
  Nat.le_zero.mp (Nat.sInf_le ⟨∅, isTriangleCover_empty G h, Set.ncard_empty _⟩)

/--
**Tuza's conjecture (1981).**

In every finite graph, if every set of pairwise edge-disjoint triangles has size at most `ν`,
then all triangles can be met by at most `2ν` edges: `τ(G) ≤ 2ν(G)`. The bound would be sharp,
e.g. for `K₄` and `K₅`.
-/
@[category research open, AMS 5]
theorem tuza_conjecture {V : Type} [Fintype V] (G : SimpleGraph V) :
    triangleCoverNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

/--
**Haxell (1999): the best known general bound.**

In every finite graph, `τ(G) ≤ (66/23) ν(G) ≈ 2.87 ν(G)`.

*Reference:* [Ha99].
-/
@[category research solved, AMS 5]
theorem tuza_conjecture.variants.haxell {V : Type} [Fintype V] (G : SimpleGraph V) :
    (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G := by
  sorry

/--
**Tuza's conjecture for triangle-free graphs.**

A triangle-free graph needs no edges to cover its triangles, so the conjectured inequality
holds trivially.
-/
@[category test, AMS 5]
theorem tuza_conjecture.variants.triangle_free {V : Type} [Fintype V] (G : SimpleGraph V)
    (h : G.CliqueFree 3) :
    triangleCoverNumber G ≤ 2 * trianglePackingNumber G := by
  rw [triangleCoverNumber_eq_zero G h]
  exact Nat.zero_le _

end TuzaConjecture
