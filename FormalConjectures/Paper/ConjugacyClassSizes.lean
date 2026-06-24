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

import FormalConjectures.Util.ProblemImports

/-!
# The $S_3$-conjecture (conjugacy classes of distinct sizes)

*References:*
* F. M. Markel, *Groups with many conjugate elements*, J. Algebra **26** (1973), 69–74.
  (Origin of the $S_3$-conjecture.)
* R. Knörr, W. Lempken, B. Thielcke, *The $S_3$-conjecture for solvable groups*,
  Israel J. Math. **91** (1995), 61–76.
* J. Zhang, *Finite groups with many conjugate elements*, J. Algebra **170** (1994), 608–624.
* Z. Arad, M. Muzychuk, A. Oliver, *On groups with conjugacy classes of distinct sizes*,
  J. Algebra **280** (2004), 537–576.
* [Conjugacy class](https://en.wikipedia.org/wiki/Conjugacy_class)

A finite group in which distinct conjugacy classes have distinct cardinalities is called an
*anti-homogeneous* group (or *ah-group*). The symmetric group $S_3$ is an ah-group: its three
conjugacy classes have sizes $1$, $2$, and $3$. Markel's **$S_3$-conjecture** (1973) asserts that,
up to isomorphism, $S_3$ is the only nontrivial finite ah-group. The conjecture has been proved
for all solvable groups (independently by Zhang and by Knörr–Lempken–Thielcke), but the general
non-solvable case remains open.
-/

namespace ConjugacyClassSizes

open ConjClasses

/--
The cardinality of the conjugacy class `c`.
-/
noncomputable def conjClassCard {G : Type*} [Monoid G] (c : ConjClasses G) : ℕ :=
  Nat.card c.carrier

/--
A finite group `G` satisfies `HasDistinctConjClassSizes` if the map assigning to each conjugacy class the
cardinality of its carrier is injective, i.e. distinct conjugacy classes have distinct sizes.

Such a group is called an *anti-homogeneous group* (or *ah-group*).
-/
def HasDistinctConjClassSizes (G : Type*) [Group G] [Fintype G] : Prop :=
  Function.Injective (conjClassCard (G := G))

/--
Equivalently, two conjugacy classes with the same cardinality must coincide.
-/
@[category API, AMS 20]
theorem hasDistinctConjClassSizes_iff {G : Type*} [Group G] [Fintype G] :
    HasDistinctConjClassSizes G ↔
      ∀ (a b : ConjClasses G), conjClassCard a = conjClassCard b → a = b := by
  simp only [HasDistinctConjClassSizes, Function.Injective]

/--
The trivial group is anti-homogeneous, since it has a single conjugacy class.
-/
@[category test, AMS 20]
theorem hasDistinctConjClassSizes_of_subsingleton {G : Type*} [Group G] [Fintype G]
    [Subsingleton G] : HasDistinctConjClassSizes (G := G) := by
  have hsub : Subsingleton (ConjClasses G) :=
    inferInstanceAs (Subsingleton (Quotient (IsConj.setoid G)))
  rw [hasDistinctConjClassSizes_iff]
  intros a b _
  exact Subsingleton.elim a b

/--
An anti-homogeneous group has trivial center, since each central element is in its own conjugacy class.
-/
@[category test, AMS 20]
theorem trivial_center_of_hasDistinctConjClassSizes {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) : Subgroup.center G = ⊥ := by
  -- A central element `w` is conjugate only to itself, so its conjugacy class is `{w}`.
  have hcard : ∀ w : G, w ∈ Subgroup.center G → conjClassCard (ConjClasses.mk w) = 1 := by
    intro w hw
    have hset : ConjClasses.carrier (ConjClasses.mk w) = {w} := by
      ext a
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨c, hc⟩
        rw [SemiconjBy] at hc
        have : c * a = c * w := by rw [hc]; exact (Subgroup.mem_center_iff.mp hw c).symm
        exact mul_left_cancel this
      · rintro rfl
        exact IsConj.refl a
    simp [conjClassCard, hset]
  -- Hence the class of any central `z` has the same size as the class of `1`, forcing `z = 1`.
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz1 : ConjClasses.mk z = ConjClasses.mk 1 := by
    apply h
    rw [hcard z hz, hcard 1 (Subgroup.one_mem _)]
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hz1
  exact isConj_one_right.mp hz1.symm

/--
The symmetric group $S_3$ is anti-homogeneous, since its three conjugacy classes have sizes $1$, $2$ and $3$.
-/
@[category test, AMS 20]
theorem hasDistinctConjClassSizes_perm_fin_three :
    HasDistinctConjClassSizes (Equiv.Perm (Fin 3)) := by
  have key : (conjClassCard (G := Equiv.Perm (Fin 3))) =
      fun c => c.carrier.toFinset.card := by
    funext c
    rw [conjClassCard, Nat.card_eq_fintype_card, ← Set.toFinset_card]
  unfold HasDistinctConjClassSizes
  rw [key]
  decide

/--
**Markel's $S_3$-conjecture** (1973): any nontrivial finite ah-group is isomorphic to $S_3$.

The conjecture is open in general; it is known to be true for solvable groups.
-/
@[category research open, AMS 20]
theorem conjClassSizes_iff_sym_three
    (G : Type) [Group G] [Fintype G] [Nontrivial G]
    (h : HasDistinctConjClassSizes (G := G)) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  sorry

/--
The $S_3$-conjecture holds for solvable groups: every nontrivial *solvable* finite ah-group is
isomorphic to $S_3$. This was proved independently by Zhang (1994) and by
Knörr–Lempken–Thielcke (1995).
-/
@[category research solved, AMS 20]
theorem conjClassSizes_iff_sym_three_solvable
    (G : Type) [Group G] [Fintype G] [IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes (G := G)) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  sorry

end ConjugacyClassSizes
