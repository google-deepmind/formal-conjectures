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

public import FormalConjecturesUtil

/-!
# Disjoint Golomb rulers

A family of disjoint Golomb rulers consists of pairwise disjoint sets of marks, each with
unique positive differences. Let $H(I,J)$ be the least positive interval size that contains
$I$ disjoint rulers with $J$ marks each. The disjoint-ruler conjecture says that every set of
$H(I,J)$ positive integers contains such a family.

*References:*
* B. Xiu, C. Fan and M. Liang,
  [On Disjoint Golomb Rulers](https://arxiv.org/abs/1405.4535), Conjecture 1.
* X. Xu, B. Xiu, C. Fan and M. Liang,
  [Some constructive results on Disjoint Golomb Rulers](https://arxiv.org/abs/2409.14409),
  Conjecture 1.
-/

@[expose] public section

namespace Arxiv.«1405.4535»

/-- A family of $I$ disjoint $J$-mark Golomb rulers contained in the finite set $A$. -/
def IsDGRFamily (I J : ℕ) (A : Finset ℕ) (R : Finset (Finset ℕ)) : Prop :=
  R.card = I ∧
    (∀ r ∈ R, r ⊆ A ∧ r.card = J ∧ IsSidon (r : Set ℕ)) ∧
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint r s

instance (I J : ℕ) (A : Finset ℕ) (R : Finset (Finset ℕ)) :
    Decidable (IsDGRFamily I J A R) := by
  unfold IsDGRFamily
  infer_instance

/-- The set $A$ contains $I$ disjoint $J$-mark Golomb rulers. -/
def HasDGRIn (I J : ℕ) (A : Finset ℕ) : Prop :=
  ∃ R : Finset (Finset ℕ), IsDGRFamily I J A R

/-- The interval $\{1,\ldots,N\}$ is the smallest positive interval admitting the family. -/
def IsLeastDGRScope (I J N : ℕ) : Prop :=
  0 < N ∧ HasDGRIn I J (Finset.Icc 1 N) ∧
    ∀ M : ℕ, 0 < M → M < N → ¬ HasDGRIn I J (Finset.Icc 1 M)

/-- A member of the family has exactly the prescribed number of marks. -/
@[category API, AMS 5 11 94]
theorem member_card {I J : ℕ} {A : Finset ℕ} {R : Finset (Finset ℕ)}
    (h : IsDGRFamily I J A R) {r : Finset ℕ} (hr : r ∈ R) : r.card = J :=
  (h.2.1 r hr).2.1

/-- The familiar ruler $\{1,2,5,7\}$ has four distinct marks and unique differences. -/
@[category test, AMS 5 11 94]
theorem four_mark_ruler :
    IsDGRFamily 1 4 {1, 2, 5, 7} {{1, 2, 5, 7}} := by
  decide

/-- Two disjoint two-mark rulers fit in the four-element interval. -/
@[category test, AMS 5 11 94]
theorem two_disjoint_pairs :
    IsDGRFamily 2 2 {1, 2, 3, 4} {{1, 2}, {3, 4}} := by
  decide

/-- The repeated distance in a three-term arithmetic progression is forbidden. -/
@[category test, AMS 5 11 94]
theorem arithmetic_progression_not_ruler :
    ¬ IsDGRFamily 1 3 {1, 2, 3} {{1, 2, 3}} := by
  decide

/-- Individual rulers may not share a mark. -/
@[category test, AMS 5 11 94]
theorem overlapping_pairs_not_disjoint :
    ¬ IsDGRFamily 2 2 {1, 2, 3} {{1, 2}, {2, 3}} := by
  decide

/-- A singleton is the smallest positive-mark ruler. -/
@[category test, AMS 5 11 94]
theorem singleton_ruler : IsDGRFamily 1 1 {1} {{1}} := by
  decide

/-- An empty family cannot represent a positive number of rulers. -/
@[category test, AMS 5 11 94]
theorem empty_family_not_one : ¬ IsDGRFamily 1 1 {1} ∅ := by
  decide

/-- Disjoint rulers may have the same distance between different pairs of marks. -/
@[category test, AMS 5 11 94]
theorem shared_distance_allowed :
    IsDGRFamily 2 2 {1, 2, 4, 5} {{1, 2}, {4, 5}} := by
  decide

/--
For positive $I$ and $J$, every set of $H(I,J)$ positive integers contains $I$ disjoint
$J$-mark Golomb rulers. Here the minimum defining $H(I,J)$ is stated explicitly.
-/
@[category research open, AMS 5 11 94]
theorem disjoint_golomb_rulers :
    ∀ I J : ℕ, 0 < I → 0 < J →
      ∃ N : ℕ, IsLeastDGRScope I J N ∧
        ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.card = N → HasDGRIn I J A := by
  sorry

end Arxiv.«1405.4535»
