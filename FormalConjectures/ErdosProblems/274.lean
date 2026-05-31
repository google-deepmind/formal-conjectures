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
* [erdosproblems.com/274](https://www.erdosproblems.com/274)
* [Wikipedia](https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture)
* [arXiv:1803.08301](https://arxiv.org/abs/1803.08301)
* [arXiv:1803.03569](https://arxiv.org/abs/1803.03569)
* [PMC7247885](https://pmc.ncbi.nlm.nih.gov/articles/PMC7247885/)
* [arXiv:1804.11103](https://arxiv.org/abs/1804.11103)
-/

open scoped Pointwise Cardinal

namespace Erdos274

-- TODO(callesonne): add already proved results from the wiki page

universe u v

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

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

inductive V4
  | e | a | b | c
  deriving DecidableEq, Fintype

namespace V4

def mul : V4 → V4 → V4
  | e, x => x
  | x, e => x
  | a, a => e
  | b, b => e
  | c, c => e
  | a, b => c
  | b, a => c
  | a, c => b
  | c, a => b
  | b, c => a
  | c, b => a

instance : One V4 := ⟨e⟩
instance : Mul V4 := ⟨mul⟩
instance : Inv V4 := ⟨id⟩
instance : Div V4 := ⟨fun x y => x * y⁻¹⟩

@[simp] lemma inv_eq (x : V4) : x⁻¹ = x := rfl

instance : Group V4 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  div_eq_mul_inv := by decide

end V4

abbrev U4 : Type u := ULift.{u, 0} V4

def u4 (x : V4) : U4 := ULift.up x

@[simp] lemma u4_down (x : V4) : (u4 x : U4).down = x := rfl
@[simp] lemma u4_e : (u4 V4.e : U4) = 1 := rfl
@[simp] lemma U4_down_one : ((1 : U4).down) = 1 := rfl
@[simp] lemma U4_down_mul (x y : U4) : (x * y).down = x.down * y.down := rfl
@[simp] lemma U4_down_inv (x : U4) : (x⁻¹).down = x.down⁻¹ := rfl

def H4 : Subgroup U4 where
  carrier := {x | x.down = V4.e ∨ x.down = V4.a}
  one_mem' := by
    left
    rfl
  mul_mem' := by
    intro x y hx hy
    cases x with
    | up x =>
      cases y with
      | up y =>
        fin_cases x <;> fin_cases y <;> simp at hx hy ⊢
        · left
          rfl
        · rfl
        · rfl
        · rfl
  inv_mem' := by
    intro x hx
    cases x with
    | up x =>
      fin_cases x <;> simp at hx ⊢

abbrev I3 : Type v := ULift.{v, 0} (Fin 3)

def i3 (i : Fin 3) : I3 := ULift.up i

def parts4 (i : I3.{v}) : Subgroup U4.{u} :=
  match i.down with
  | 0 => H4
  | 1 => ⊥
  | 2 => ⊥

def reps4 (i : I3.{v}) : U4.{u} :=
  match i.down with
  | 0 => u4 V4.e
  | 1 => u4 V4.b
  | 2 => u4 V4.c

private theorem erdos_274_witness :
    ∃ (G : Type u) (_ : Group G) (_ : 1 < ENat.card G)
      (ι : Type v) (_ : Fintype ι) (P : Group.ExactCovering G ι),
        1 < Fintype.card ι ∧ ∃ i j, i ≠ j ∧ #(P.parts i) ≠ #(P.parts j) := by
  refine Exists.intro U4.{u} ?_
  refine Exists.intro (inferInstanceAs (Group U4.{u})) ?_
  refine ⟨?_, I3.{v}, inferInstance, ?_, ?_⟩
  · rw [ENat.card_eq_coe_fintype_card]
    rw [Fintype.card_ulift]
    decide +kernel
  · refine
      { parts := (parts4.{u, v})
        reps := (reps4.{u, v})
        nonempty := ?_
        disjoint := ?_
        covers := ?_ }
    · intro i
      exact ⟨1, Subgroup.one_mem _⟩
    · rw [Set.pairwiseDisjoint_iff]
      intro i _ j _ hne
      cases i with
      | up i =>
        cases j with
        | up j =>
          fin_cases i <;> fin_cases j <;>
            simp [parts4, reps4, H4, u4, Set.mem_smul_set_iff_inv_smul_mem] at hne ⊢
          all_goals
            cases hne
    · ext x
      cases x with
      | up x =>
        fin_cases x
        all_goals simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        · refine ⟨i3 0, ?_⟩
          change (u4 V4.e : U4.{u}) ∈ u4 V4.e • (H4.{u} : Set U4.{u})
          exact Set.mem_smul_set.mpr
            ⟨1, Subgroup.one_mem (H4.{u} : Subgroup U4.{u}), by simp⟩
        · refine ⟨i3 0, ?_⟩
          change (u4 V4.a : U4.{u}) ∈ u4 V4.e • (H4.{u} : Set U4.{u})
          exact Set.mem_smul_set.mpr ⟨u4 V4.a, by right; rfl, by simp [u4_e]⟩
        · refine ⟨i3 1, ?_⟩
          change (u4 V4.b : U4.{u}) ∈ u4 V4.b • ((⊥ : Subgroup U4.{u}) : Set U4.{u})
          exact Set.mem_smul_set.mpr ⟨1, Subgroup.one_mem _, by simp⟩
        · refine ⟨i3 2, ?_⟩
          change (u4 V4.c : U4.{u}) ∈ u4 V4.c • ((⊥ : Subgroup U4.{u}) : Set U4.{u})
          exact Set.mem_smul_set.mpr ⟨1, Subgroup.one_mem _, by simp⟩
  · constructor
    · norm_num [I3]
    · refine ⟨i3 0, i3 1, ?_, ?_⟩
      · decide
      · change #(H4.{u} : Subgroup U4.{u}) ≠ #((⊥ : Subgroup U4.{u}))
        classical
        letI : Fintype (H4.{u} : Subgroup U4.{u}) :=
          Fintype.ofFinite (H4.{u} : Subgroup U4.{u})
        letI : Fintype (⊥ : Subgroup U4.{u}) := Fintype.ofFinite (⊥ : Subgroup U4.{u})
        rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
        change (Fintype.card H4.{u} : Cardinal) ≠
          (Fintype.card (⊥ : Subgroup U4.{u}) : Cardinal)
        norm_num
        intro hcard
        have hle : Fintype.card (H4.{u} : Subgroup U4.{u}) ≤ 1 := by omega
        haveI : Subsingleton (H4.{u} : Subgroup U4.{u}) :=
          Fintype.card_le_one_iff_subsingleton.mp hle
        have heq :
            (⟨u4 V4.e, by left; rfl⟩ : (H4.{u} : Subgroup U4.{u})) =
              ⟨u4 V4.a, by right; rfl⟩ :=
          Subsingleton.elim _ _
        have : V4.e = V4.a :=
          congrArg (fun x : (H4.{u} : Subgroup U4.{u}) => x.1.down) heq
        cases this

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true

/--
Does there exist a group `G` with an exact covering by more than one cosets of
different sizes? (i.e. each element is contained in exactly one of the cosets.)
-/
@[category research solved, AMS 20]
theorem erdos_274 : answer(True) ↔ ∃ (G : Type*) (h : Group G) (hG : 1 < ENat.card G)
    (ι : Type*) (_ : Fintype ι) (P : Group.ExactCovering G ι),
      1 < Fintype.card ι ∧ ∃ i j, i ≠ j ∧ #(P.parts i) ≠ #(P.parts j) := by
  show True ↔ _
  exact ⟨fun _ ↦ erdos_274_witness, fun _ ↦ trivial⟩

/--
If `G` is a finite abelian group then there cannot exist an exact covering of `G` by more
than one cosets of different sizes? (i.e. each element is contained in exactly one
of the cosets.)
-/
@[category research solved, AMS 20]
theorem erdos_274.variants.abelian {G : Type*} [Fintype G] [CommGroup G]
    (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι] (P : Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
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
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  sorry

end Erdos274
