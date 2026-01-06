/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 274

*References:*
[erdosproblems.com/274](https://www.erdosproblems.com/274)
[Wikipedia](https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture)
-/

open scoped Pointwise Cardinal

namespace Erdos274

-- TODO(callesonne): add already proved results from the wiki page

/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`.

Note that this differs from `Partition (α := Subgroup G)` because the covering condition there
invokes `Subgroup.sup` which is subgroup generation and thus stronger than union. This definition
is easier to use in this contect than the alternative `Partition (α := Set G)`, which lacks
subgroup definitions such as `Subgroup.index`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  parts : ι → Subgroup G
  reps : ι → G
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

/--
If `G` is a group then can there exist an exact covering of `G` by more than one cosets of
different sizes? (i.e. each element is contained in exactly one of the cosets.)
-/
@[category research open, AMS 20]
theorem erdos_274 : answer(sorry) ↔ ∀ᵉ (G : Type*) (h : Group G) (hG : 1 < ENat.card G),
    (∃ (ι : Type*) (_ : Fintype ι) (P : Group.ExactCovering G ι),
      1 < Fintype.card ι ∧ (Set.range P.parts).Pairwise fun A B ↦ #A ≠ #B) := by
  sorry

/--
If `G` is a finite abelian group then there cannot exist an exact covering of `G` by more
than one cosets of different sizes? (i.e. each element is contained in exactly one
of the cosets.)
-/
@[category research solved, AMS 20]
theorem erdos_274.variants.abelian {G : Type*} [Fintype G] [CommGroup G]
    (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι] (P : Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) :
    ∃ i j, P.parts i ≠ P.parts j ∧ #(P.parts i) = #(P.parts j) := by
  sorry

/--
Let $G$ be a group, and let $A = \{a_1G_1, \dots, a_kG_k\}$ be a finite system of left cosets of
subgroups $G_1, \dots, G_k$ of $G$.

Herzog and Schönheim conjectured that if $A$ forms a partition of $G$ with $k > 1$, then the
indices $[G:G_1], \dots, [G:G_k]$ cannot be distinct.
-/
@[category research open, AMS 20]
theorem herzog_schonheim {G : Type*} [Group G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Group.ExactCovering G ι) :
    ∃ i j, P.parts i ≠ P.parts j ∧ (P.parts i).index = (P.parts j).index := by
  sorry

end Erdos274
