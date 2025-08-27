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

-- TODO(callesonne): add already proved results from the wiki page

/--
If `G` is an abelian group then can there exist an exact covering of `G` by more than one cosets of
different sizes? (i.e. each element is contained in exactly one of the cosets.)
-/
@[category research open, AMS 20]
theorem erdos_274 :
    (∀ (G : Type*), [CommGroup G] →
    ∃ (P : Partition (⊤ : Subgroup G)), 1 < P.parts.ncard ∧
      (∀ A ∈ P.parts, ∃ (s : G) (H : Subgroup G), s • (H : Set G) = A) ∧
      P.parts.Pairwise fun A B ↦ #A ≠ #B) ↔ answer(sorry) := by
  sorry

/--
In [Er97c] Erdős asks this for finite (not necessarily abelian) groups.

[Er97c] Erdős, Paul, Some of my favorite problems and results.
The mathematics of Paul Erd\H{o}s, I (1997), 47-67.
-/
@[category research open, AMS 20]
theorem erdos_274.variants.nonabelian :
    (∀ (G : Type*), [Group G] → [Fintype G] →
    ∃ (P : Partition (⊤ : Subgroup G)),
      1 < P.parts.ncard ∧
      (∀ A ∈ P.parts, ∃ᵉ (s : G) (H : Subgroup G), s • (H : Set G) = A) ∧
      P.parts.Pairwise fun A B ↦ #A ≠ #B) ↔ answer(sorry) := by
  sorry


/--
Let $G$ be a group, and let $A = \{a_1G_1, \dots, a_kG_k\}$ be a finite system of left cosets of
subgroups $G_1, \dots, G_k$ of $G$.

Herzog and Schönheim conjectured that if $A$ forms a partition of $G$ with $k > 1$, then the
indices $[G:G_1], \dots, [G:G_k]$ cannot be distinct.
-/
@[category research open, AMS 20]
theorem herzog_schonheim (G : Type*) [Group G] : ∀ (P : Partition (⊤ : Subgroup G)),
    1 < P.parts.ncard →
    (∀ B ∈ P.parts, ∃ (s : G) (H : Subgroup G), s • (H : Set G) = B) →
    ∃ᵉ (A ∈ P.parts) (B ∈ P.parts), A ≠ B ∧ A.index = B.index := by
  sorry
