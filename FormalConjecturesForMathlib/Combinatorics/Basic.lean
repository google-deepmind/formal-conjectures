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
module

public import FormalConjecturesForMathlib.Combinatorics.AP.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open Function Set
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is said to be product-free if the product set $S \cdot S$ is disjoint from $S$,
i.e. if the equation $x \cdot y = z$ has no solution with $x, y, z \in S$.
-/
@[to_additive IsSumFree /--
A set $A$ is said to be sum-free if the sumset $A + A$ is disjoint from $A$, i.e.
if the equation $a + b = c$ has no solution with $a, b, c \in A$.
-/]
def IsProductFree {M : Type*} [Mul M] (S : Set M) : Prop := Disjoint (S * S) S

@[to_additive isSumFree_iff]
theorem isProductFree_iff {M : Type*} [Mul M] {S : Set M} :
    IsProductFree S ↔ ∀ x ∈ S, ∀ y ∈ S, x * y ∉ S := by
  simp [IsProductFree, Set.disjoint_left, Set.mem_mul]
  aesop

/--
`allUniqueSums A` is the set of elements in `α` that can be written as the sum of exactly one
unordered pair of elements from `A`.
-/
def allUniqueSums (A : Set α) : Set α :=
  { n | ∃ p : α × α, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
      ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n → (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1) }

/--
A set `A` has no unique representation in its sumset `A + A` if for every pair of elements
`a₁, a₂ ∈ A`, there exist another pair of elements `b₁, b₂ ∈ A` such that `a₁ + a₂ = b₁ + b₂`
and `{a₁, a₂} ≠ {b₁, b₂}`.
-/
def HasNoUniqueRepresentation {α : Type*} [AddCommMonoid α] (A : Finset α) : Prop :=
  allUniqueSums (A : Set α) = ∅

/-- A set $A$ of natural numbers is said to have bounded gaps if there exists an integer $p$ such
that $A ∩ [n, n + 1, ..., n + p]$ is nonempty for all $n$. -/
def IsSyndetic (A : Set ℕ) : Prop := ∃ p, ∀ n, (A ∩ .Icc n (n + p)).Nonempty

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

lemma IsSidon.avoids_isAPOfLength_three {A : Set ℕ} (hA : IsSidon A)
    {Y : Set ℕ} (hY : Y.IsAPOfLength 3) :
    (A ∩ Y).ncard ≤ 2 := by
  simp [IsAPOfLength, IsAPOfLengthWith] at hY
  obtain ⟨hc, ⟨a, d, hY⟩⟩ := hY
  have hY_card : Y.ncard = 3 := by simp [ncard, hc]
  by_contra! h
  have hss : Y ⊆ A ∩ Y := by
    have hY_fin : Finite Y := finite_of_ncard_ne_zero (by linarith)
    rw [Set.eq_of_subset_of_ncard_le (Set.inter_subset_right) (by linarith)]
  have ha : a ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨0, by norm_num, by simp⟩)
  have ha₁ : a + d ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨1, by norm_num, by simp⟩)
  have ha₂ : a + 2 • d ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨2, by norm_num, by simp⟩)
  have := hA _ ha _ ha₁ _ ha₂ _ ha₁ (by simp; omega)
  simp at this
  simp [hY, this.1, ofPred_and] at hY_card
  linarith [ncard_singleton _ ▸ ncard_inter_le_ncard_right {a | ∃ x, x < 3} {a}]

theorem IsSidon.subset {A B : Set α} (hB : IsSidon B) (hAB : A ⊆ B) : IsSidon A :=
  fun _ _ _ _ _ _ _ _ _ ↦ hB _ (hAB ‹_›) _ (hAB ‹_›) _ (hAB ‹_›) _ (hAB ‹_›) ‹_›

theorem IsSidon.insert {A : Set α} {m : α} [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔ (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]


/-!
Maximal Sidon sets in an interval.

We follow the convention that `IsMaximalSidonSetIn A N` means `A ⊆ {1, …, N}` is Sidon and
is inclusion-maximal among subsets of `Set.Icc 1 N` with the Sidon property.
-/

/-- `IsMaximalSidonSetIn A N` means `A ⊆ {1, …, N}` is Sidon and cannot be extended within
`{1, …, N}` while remaining Sidon. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ ⦃x : ℕ⦄, x ∈ Set.Icc 1 N → x ∉ A → ¬ IsSidon (A ∪ {x})

namespace IsMaximalSidonSetIn

/-- If `A` is a maximal Sidon set in `{1, …, N}`, then `A ⊆ {1, …, N}`. -/
theorem subset {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) :
    A ⊆ Set.Icc 1 N := hA.1

/-- If `A` is a maximal Sidon set in `{1, …, N}`, then `A` is Sidon. -/
theorem isSidon {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) : IsSidon A := hA.2.1

/-- Maximality condition unpacked. -/
theorem maximal {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) {x : ℕ}
    (hx : x ∈ Set.Icc 1 N) (hxA : x ∉ A) : ¬ IsSidon (A ∪ {x}) := hA.2.2 hx hxA

end IsMaximalSidonSetIn

end Set

namespace Finset

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl


/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

/-- The number of Sidon subsets of the supplied `Finset`. -/
def sidonSubsetCount (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).card

/-- The empty set is always Sidon, so there is at least one Sidon subset. -/
theorem sidonSubsetCount_pos (A : Finset α) [DecidableEq α] : 0 < sidonSubsetCount A := by
  refine card_pos.mpr ⟨∅, ?_⟩
  simp [IsSidon]

/-- Alias: `1 ≤ sidonSubsetCount A`. -/
theorem one_le_sidonSubsetCount (A : Finset α) [DecidableEq α] : 1 ≤ sidonSubsetCount A :=
  Nat.succ_le_iff.mpr (sidonSubsetCount_pos A)

/-- Any maximum-size Sidon subset `B` contributes `2 ^ |B|` Sidon subsets via
`IsSidon.subset`, so `2 ^ maxSidonSubsetCard A ≤ sidonSubsetCount A`. -/
theorem two_pow_maxSidonSubsetCard_le_sidonSubsetCount (A : Finset α) [DecidableEq α] :
    2 ^ maxSidonSubsetCard A ≤ sidonSubsetCount A := by
  let S := A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)
  have hS : S.Nonempty := ⟨∅, by simp [S, IsSidon]⟩
  obtain ⟨B, hB, hBcard⟩ := exists_mem_eq_sup S hS Finset.card
  have hB' := mem_filter.mp hB
  have hsub : B.powerset ⊆ S := by
    intro C hC
    rw [mem_powerset] at hC
    exact mem_filter.mpr ⟨mem_powerset.mpr (hC.trans (mem_powerset.mp hB'.1)),
      IsSidon.subset hB'.2 (by simpa using hC)⟩
  calc
    2 ^ maxSidonSubsetCard A = 2 ^ B.card := by rw [← hBcard]; rfl
    _ = B.powerset.card := (card_powerset B).symm
    _ ≤ S.card := card_le_card hsub
    _ = sidonSubsetCount A := rfl

/-- A Sidon subset cannot be larger than the ambient set. -/
theorem maxSidonSubsetCard_le_card (A : Finset α) [DecidableEq α] :
    maxSidonSubsetCard A ≤ A.card := by
  classical
  refine Finset.sup_le ?_
  intro B hB
  exact card_le_card (mem_powerset.mp (mem_filter.mp hB).1)

/-- At most all subsets of `A` are Sidon. -/
theorem sidonSubsetCount_le_two_pow_card (A : Finset α) [DecidableEq α] :
    sidonSubsetCount A ≤ 2 ^ A.card := by
  classical
  simpa [sidonSubsetCount, card_powerset] using
    card_le_card (filter_subset (fun B : Finset α ↦ IsSidon (B : Set α)) A.powerset)

@[simp]
theorem maxSidonSubsetCard_empty [DecidableEq α] : maxSidonSubsetCard (∅ : Finset α) = 0 := by
  classical
  simp [maxSidonSubsetCard]

@[simp]
theorem sidonSubsetCount_empty [DecidableEq α] : sidonSubsetCount (∅ : Finset α) = 1 := by
  classical
  have : (∅ : Finset α).powerset = {∅} := by simp
  simp [sidonSubsetCount, this, filter_singleton, IsSidon]

/-- Enlarging the ambient set cannot decrease the max Sidon subset size. -/
theorem maxSidonSubsetCard_mono {A B : Finset α} [DecidableEq α] (h : A ⊆ B) :
    maxSidonSubsetCard A ≤ maxSidonSubsetCard B := by
  classical
  refine Finset.sup_le fun C hC ↦ ?_
  have hC' := mem_filter.mp hC
  have hCB : C ∈ B.powerset.filter fun D : Finset α ↦ IsSidon (D : Set α) := by
    exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hC'.1).trans h), hC'.2⟩
  exact le_sup hCB

/-- Enlarging the ambient set cannot decrease the number of Sidon subsets. -/
theorem sidonSubsetCount_mono {A B : Finset α} [DecidableEq α] (h : A ⊆ B) :
    sidonSubsetCount A ≤ sidonSubsetCount B := by
  classical
  refine card_le_card ?_
  intro C hC
  have hC' := mem_filter.mp hC
  exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hC'.1).trans h), hC'.2⟩

/-- Any Sidon subset `B ⊆ A` contributes `2 ^ #B` Sidon subsets of `A`. -/
theorem two_pow_card_le_sidonSubsetCount_of_isSidon {A B : Finset α} [DecidableEq α]
    (hBA : B ⊆ A) (hB : IsSidon (B : Set α)) :
    2 ^ B.card ≤ sidonSubsetCount A := by
  classical
  have hsub : B.powerset ⊆ A.powerset.filter fun C : Finset α ↦ IsSidon (C : Set α) := by
    intro C hC
    exact mem_filter.mpr
      ⟨mem_powerset.mpr ((mem_powerset.mp hC).trans hBA),
        IsSidon.subset hB (mem_powerset.mp hC)⟩
  calc
    2 ^ B.card = B.powerset.card := (card_powerset B).symm
    _ ≤ (A.powerset.filter fun C : Finset α ↦ IsSidon (C : Set α)).card := card_le_card hsub
    _ = sidonSubsetCount A := rfl

/-- Any Sidon subset of `A` has size at most `maxSidonSubsetCard A`. -/
theorem card_le_maxSidonSubsetCard {A B : Finset α} [DecidableEq α]
    (hBA : B ⊆ A) (hB : IsSidon (B : Set α)) :
    B.card ≤ maxSidonSubsetCard A := by
  classical
  have h : B ∈ A.powerset.filter fun C : Finset α ↦ IsSidon (C : Set α) :=
    mem_filter.mpr ⟨mem_powerset.mpr hBA, hB⟩
  exact le_sup (f := Finset.card) h

lemma IsSidon.singleton (a : α) : IsSidon ({a} : Set α) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  subst hi₁; subst hj₁; subst hi₂; subst hj₂
  exact Or.inl ⟨rfl, rfl⟩

/-- Nonempty ambient sets admit a Sidon singleton, so the max size is at least `1`. -/
theorem one_le_maxSidonSubsetCard_of_nonempty [DecidableEq α] {A : Finset α}
    (hA : A.Nonempty) : 1 ≤ maxSidonSubsetCard A := by
  classical
  obtain ⟨a, ha⟩ := hA
  have hsub : ({a} : Finset α) ⊆ A := singleton_subset_iff.mpr ha
  have hsid : IsSidon (({a} : Finset α) : Set α) := by
    rw [coe_singleton]
    exact IsSidon.singleton a
  simpa using card_le_maxSidonSubsetCard hsub hsid

/-- `maxSidonSubsetCard A = 0` if and only if `A` is empty. -/
theorem maxSidonSubsetCard_eq_zero_iff [DecidableEq α] (A : Finset α) :
    maxSidonSubsetCard A = 0 ↔ A = ∅ := by
  classical
  constructor
  · intro h
    by_contra hne
    have : 1 ≤ maxSidonSubsetCard A :=
      one_le_maxSidonSubsetCard_of_nonempty (nonempty_iff_ne_empty.mpr hne)
    omega
  · rintro rfl
    simp

/-- `sidonSubsetCount A = 1` if and only if `A` is empty. -/
theorem sidonSubsetCount_eq_one_iff [DecidableEq α] (A : Finset α) :
    sidonSubsetCount A = 1 ↔ A = ∅ := by
  classical
  constructor
  · intro h
    by_contra hne
    obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hne
    have hsub : ({a} : Finset α) ⊆ A := singleton_subset_iff.mpr ha
    have hsid : IsSidon (({a} : Finset α) : Set α) := by
      rw [coe_singleton]
      exact IsSidon.singleton a
    have : 2 ≤ sidonSubsetCount A := by
      simpa using two_pow_card_le_sidonSubsetCount_of_isSidon hsub hsid
    omega
  · rintro rfl
    simp

@[simp]
theorem maxSidonSubsetCard_singleton [DecidableEq α] (a : α) :
    maxSidonSubsetCard ({a} : Finset α) = 1 := by
  classical
  refine le_antisymm (maxSidonSubsetCard_le_card _) ?_
  have h : ({a} : Finset α) ∈ ({a} : Finset α).powerset.filter fun B : Finset α ↦
      IsSidon (B : Set α) :=
    mem_filter.mpr ⟨mem_powerset_self _, by simpa using IsSidon.singleton a⟩
  exact le_sup (f := Finset.card) h

@[simp]
theorem sidonSubsetCount_singleton [DecidableEq α] (a : α) :
    sidonSubsetCount ({a} : Finset α) = 2 := by
  classical
  have hEmpty : IsSidon ((∅ : Finset α) : Set α) := by simp [IsSidon]
  have ha : IsSidon (({a} : Finset α) : Set α) := by simpa using IsSidon.singleton a
  have hp : ({a} : Finset α).powerset = {∅, {a}} := by
    ext x
    simp [mem_powerset, subset_singleton_iff]
  have hne : (∅ : Finset α) ≠ {a} := Ne.symm (singleton_ne_empty a)
  simp only [sidonSubsetCount, hp, filter_insert, if_pos hEmpty, filter_singleton, if_pos ha]
  rw [card_insert_of_notMem (by simp [hne]), card_singleton]

/-- The empty set is Sidon. -/
lemma IsSidon.empty : IsSidon (∅ : Set α) := by
  simp [IsSidon]

/-- Any set with at most one element is Sidon. -/
lemma IsSidon.of_subsingleton {A : Set α} (hA : A.Subsingleton) : IsSidon A := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
  exact Or.inl ⟨hA hi₁ hj₁, hA hi₂ hj₂⟩

/-- Finite sets of cardinality at most `1` are Sidon. -/
lemma IsSidon.of_card_le_one [DecidableEq α] {A : Finset α} (hA : A.card ≤ 1) :
    IsSidon (A : Set α) :=
  IsSidon.of_subsingleton (card_le_one_iff_subsingleton.mp hA)

/-- On `ℕ`, any Finset of size at most `2` is Sidon. -/
lemma IsSidon.of_card_le_two {A : Finset ℕ} (hA : A.card ≤ 2) :
    IsSidon (A : Set ℕ) := by
  classical
  by_cases h1 : A.card ≤ 1
  · exact IsSidon.of_card_le_one h1
  · have h2 : A.card = 2 := by omega
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    intro a ha b hb c hc d hd hs
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hc with hc | hc <;> rcases hd with hd | hd <;>
      subst_vars <;> try exact Or.inl ⟨rfl, rfl⟩
    all_goals
      try exact Or.inr ⟨rfl, rfl⟩
      try exact (hxy (by omega)).elim
      try exact (hxy hs).elim
      try exact (hxy hs.symm).elim

/-- If `A` itself is Sidon, the largest Sidon subset has size `#A`. -/
theorem maxSidonSubsetCard_eq_card [DecidableEq α] {A : Finset α}
    (hA : IsSidon (A : Set α)) : maxSidonSubsetCard A = A.card := by
  classical
  refine le_antisymm (maxSidonSubsetCard_le_card _) ?_
  have h : A ∈ A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α) :=
    mem_filter.mpr ⟨mem_powerset_self _, hA⟩
  exact le_sup (f := Finset.card) h

/-- If `A` itself is Sidon, every subset is Sidon, so there are `2 ^ #A` Sidon subsets. -/
theorem sidonSubsetCount_eq_two_pow_card [DecidableEq α] {A : Finset α}
    (hA : IsSidon (A : Set α)) : sidonSubsetCount A = 2 ^ A.card := by
  classical
  have hEq : A.powerset.filter (fun B : Finset α ↦ IsSidon (B : Set α)) = A.powerset := by
    ext B
    simp only [mem_filter, mem_powerset]
    exact ⟨And.left, fun hBA ↦ ⟨hBA, IsSidon.subset hA hBA⟩⟩
  simp [sidonSubsetCount, hEq, card_powerset]

/-- Consequently `maxSidonSubsetCard A = #A` whenever `#A ≤ 2` on `ℕ`. -/
theorem maxSidonSubsetCard_eq_card_of_card_le_two {A : Finset ℕ} [DecidableEq ℕ]
    (hA : A.card ≤ 2) : maxSidonSubsetCard A = A.card :=
  maxSidonSubsetCard_eq_card (IsSidon.of_card_le_two hA)

/-- And `sidonSubsetCount A = 2 ^ #A` whenever `#A ≤ 2` on `ℕ`. -/
theorem sidonSubsetCount_eq_two_pow_card_of_card_le_two {A : Finset ℕ} [DecidableEq ℕ]
    (hA : A.card ≤ 2) : sidonSubsetCount A = 2 ^ A.card :=
  sidonSubsetCount_eq_two_pow_card (IsSidon.of_card_le_two hA)

/-- If `A` is Sidon then `maxSidonSubsetCard` and `sidonSubsetCount` attain the trivial upper bounds. -/
theorem maxSidonSubsetCard_eq_card_iff_isSidon [DecidableEq α] (A : Finset α)
    [Decidable (IsSidon (A : Set α))] :
    maxSidonSubsetCard A = A.card ↔ IsSidon (A : Set α) := by
  classical
  constructor
  · intro h
    -- a max-size Sidon subset of size #A must be A itself
    let S := A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)
    have hS : S.Nonempty := ⟨∅, by simp [S, IsSidon]⟩
    obtain ⟨B, hB, hBcard⟩ := exists_mem_eq_sup S hS Finset.card
    have hB' := mem_filter.mp hB
    have hcard : B.card = A.card := by
      rw [← h, ← hBcard]; rfl
    have hBA : B ⊆ A := mem_powerset.mp hB'.1
    have hBA_eq : B = A := eq_of_subset_of_card_le hBA (by omega)
    exact hBA_eq ▸ hB'.2
  · exact maxSidonSubsetCard_eq_card

/-- `sidonSubsetCount A = 2 ^ #A` if and only if `A` itself is Sidon. -/
theorem sidonSubsetCount_eq_two_pow_card_iff [DecidableEq α] (A : Finset α)
    [Decidable (IsSidon (A : Set α))] :
    sidonSubsetCount A = 2 ^ A.card ↔ IsSidon (A : Set α) := by
  classical
  constructor
  · intro h
    have hcard :
        (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).card = A.powerset.card := by
      simpa [sidonSubsetCount, card_powerset] using h
    have hle : A.powerset.card ≤
        (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).card := by
      omega
    have heq :
        A.powerset.filter (fun B : Finset α ↦ IsSidon (B : Set α)) = A.powerset :=
      eq_of_subset_of_card_le (filter_subset _ _) hle
    have hA : A ∈ A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α) := by
      rw [heq]; exact mem_powerset_self A
    exact (mem_filter.mp hA).2
  · exact sidonSubsetCount_eq_two_pow_card

/-- If `A` is finite Sidon, then `A ∪ {s}` is also Sidon provided `s ≥ A.max + 1`. -/
theorem IsSidon.insert_ge_max' {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) {s : ℕ}
    (hs : 2 * A.max' h + 1 ≤ s) :
    IsSidon (A ∪ {s}) := by
  have h₁ {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
        a + b < 2 * A.max' h + 1 + c := by linarith [A.le_max' _ ha, A.le_max' _ hb]
  have : s ∉ A := by
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  exact (IsSidon.insert hA).2 <| by simpa [this] using fun a ha b hb ↦
    ⟨by linarith [A.le_max' _ ha, A.le_max' _ hb], fun c hc ↦ by linarith [h₁ hc hb ha]⟩

theorem IsSidon.exists_insert {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) :
    ∃ m ∉ A, IsSidon (A ∪ {m}) := by
  refine ⟨2 * A.max' h + 1, ?_, insert_ge_max' h hA le_rfl⟩
  exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
    linarith [A.le_max' _ ha]

theorem IsSidon.exists_insert_ge {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) (s : ℕ) :
    ∃ m ≥ s, m ∉ A ∧ IsSidon (A ∪ {m}) := by
  refine ⟨if s ≥ 2 * A.max' h + 1 then s else 2 * A.max' h + 1, ?_, ?_, ?_⟩
  · split_ifs <;> linarith
  · split_ifs <;>
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  · split_ifs with hs
    · exact insert_ge_max' h hA hs
    · exact insert_ge_max' h hA le_rfl

/-- Given a finite Sidon set `A` and a lower bound `m`, `go` finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. If `A` is empty then this returns the value `m`. Note that
the lower bound is required to avoid `0` being a contender in some cases. -/
def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    have : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using Finset.IsSidon.exists_insert_ge h hA m
    ⟨Nat.find this, Nat.find_spec this⟩
  else ⟨m, by simp_all [IsSidon]⟩

/-- Main search loop for generating the greedy Sidon sequence. The return value for step `n` is the
finite set of numbers generated so far, a proof that it is Sidon, and the greatest element of
the finite set at that point. This is initialised at `{1}`, then `greedySidon.go` is
called iteratively using the lower bound `max + 1` to find the next smallest Sidon preserving
number. -/
def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A.1 ∪ {s'.1}, s'.2.2.2⟩, s'.1)

/-- `greedySidon` is the sequence obtained by the initial set $\{1\}$ and iteratively obtaining
the next smallest integer that preserves the Sidon property of the set. This gives the
sequence `1, 2, 4, 8, 13, 21, 31, ...`. -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

/-- The greedy Sidon set in `{1, …, N}`: starting from `∅`, iterate through `1, …, N` and
include `x` if and only if `A ∪ {x}` remains Sidon.
Alternatively, this is precisely the set of elements in the greedy Sidon sequence that are `≤ N`. -/
def greedySidonBelow (N : ℕ) : Finset ℕ :=
  (greedySidon.aux N).1.1.filter (· ≤ N)

/-- The finite set produced by `greedySidon.aux` is always Sidon. -/
theorem greedySidon.aux_isSidon (n : ℕ) : IsSidon ((greedySidon.aux n).1.1 : Set ℕ) :=
  (greedySidon.aux n).1.2

/-- `greedySidonBelow N` is Sidon (as a subset of a Sidon set). -/
theorem greedySidonBelow_isSidon (N : ℕ) : IsSidon ((greedySidonBelow N) : Set ℕ) :=
  IsSidon.subset (greedySidon.aux_isSidon N) <| by
    intro x hx
    simp only [greedySidonBelow, mem_coe, mem_filter] at hx ⊢
    exact hx.1


/-- The Sidon set grows when the greedy step advances. -/
lemma greedySidon.aux_subset_succ (n : ℕ) :
    (greedySidon.aux n).1.1 ⊆ (greedySidon.aux (n + 1)).1.1 := by
  intro x hx
  dsimp [greedySidon.aux]
  exact Finset.mem_union_left _ hx

/-- Monotonicity of the finite greedy Sidon sets in the step index. -/
lemma greedySidon.aux_mono {m n : ℕ} (hmn : m ≤ n) :
    (greedySidon.aux m).1.1 ⊆ (greedySidon.aux n).1.1 := by
  induction n with
  | zero =>
    have : m = 0 := Nat.eq_zero_of_le_zero hmn
    subst this
    exact Subset.rfl
  | succ n ih =>
    have hcases : m ≤ n ∨ m = n + 1 := Nat.le_succ_iff.mp hmn
    cases hcases with
    | inl hmn' => exact (ih hmn').trans (aux_subset_succ n)
    | inr hm =>
      subst hm
      exact Subset.rfl

/-- The value `greedySidon n` is a member of the set at step `n`. -/
lemma greedySidon.mem_aux (n : ℕ) : greedySidon n ∈ (greedySidon.aux n).1.1 := by
  cases n with
  | zero =>
    change (greedySidon.aux 0).2 ∈ (greedySidon.aux 0).1.1
    simp [greedySidon.aux]
  | succ n =>
    change (greedySidon.aux (n + 1)).2 ∈ (greedySidon.aux (n + 1)).1.1
    dsimp [greedySidon.aux]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Hence `greedySidon m` lies in the set at every later step `n ≥ m`. -/
lemma greedySidon.mem_aux_of_le {m n : ℕ} (hmn : m ≤ n) :
    greedySidon m ∈ (greedySidon.aux n).1.1 :=
  aux_mono hmn (mem_aux m)

/-- Membership in `greedySidonBelow`. -/
lemma mem_greedySidonBelow {N x : ℕ} :
    x ∈ greedySidonBelow N ↔ x ∈ (greedySidon.aux N).1.1 ∧ x ≤ N := by
  simp [greedySidonBelow]

/-- The infinite greedy Sidon sequence has Sidon range. -/
theorem isSidon_range_greedySidon : IsSidon (Set.range greedySidon) := by
  intro a ha b hb c hc d hd hsum
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  obtain ⟨j, rfl⟩ := Set.mem_range.mp hb
  obtain ⟨k, rfl⟩ := Set.mem_range.mp hc
  obtain ⟨l, rfl⟩ := Set.mem_range.mp hd
  let N := max (max i j) (max k l)
  have hi : i ≤ N := by omega
  have hj : j ≤ N := by omega
  have hk : k ≤ N := by omega
  have hl : l ≤ N := by omega
  refine greedySidon.aux_isSidon N
    (greedySidon i) ?_ (greedySidon j) ?_ (greedySidon k) ?_ (greedySidon l) ?_ hsum
  · simpa using greedySidon.mem_aux_of_le hi
  · simpa using greedySidon.mem_aux_of_le hj
  · simpa using greedySidon.mem_aux_of_le hk
  · simpa using greedySidon.mem_aux_of_le hl


/-- The greedy Sidon sequence starts at `1`. -/
@[simp] lemma greedySidon_zero : greedySidon 0 = 1 := by
  simp [greedySidon, greedySidon.aux]

/-- At step `0` the finite set is `{1}`. -/
lemma greedySidon.aux_zero : (greedySidon.aux 0).1.1 = ({1} : Finset ℕ) := by
  simp [greedySidon.aux]

/-- Each greedy step adds exactly one new element, so `#aux n = n + 1`. -/
lemma greedySidon.card_aux (n : ℕ) : (greedySidon.aux n).1.1.card = n + 1 := by
  induction n with
  | zero => simp [aux_zero]
  | succ n ih =>
    dsimp [greedySidon.aux]
    set A := (greedySidon.aux n).1.1 with hAeq
    set hA := (greedySidon.aux n).1.2
    set s := if h : A.Nonempty then A.max' h + 1 else (greedySidon.aux n).2
    set s' := greedySidon.go A hA s with hs'
    have hs'notin : s'.1 ∉ A := s'.2.2.1
    change (A ∪ {s'.1}).card = n + 1 + 1
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hs'notin),
      Finset.card_singleton, ih]

/-- `greedySidon (n + 1)` is strictly larger than `greedySidon n`. -/
lemma greedySidon.lt_succ (n : ℕ) : greedySidon n < greedySidon (n + 1) := by
  change (greedySidon.aux n).2 < (greedySidon.aux (n + 1)).2
  dsimp [greedySidon.aux]
  set A := (greedySidon.aux n).1.1
  set hA := (greedySidon.aux n).1.2
  set s0 := (greedySidon.aux n).2
  set s := if h : A.Nonempty then A.max' h + 1 else s0
  set s' := greedySidon.go A hA s
  have hs'ge : s ≤ s'.1 := s'.2.1
  have hmem : s0 ∈ A := by
    simpa [greedySidon, A, s0] using greedySidon.mem_aux n
  have hAne : A.Nonempty := ⟨s0, hmem⟩
  have hs_eq : s = A.max' hAne + 1 := by simp [s, hAne]
  have : s0 < s := by
    rw [hs_eq]
    exact Nat.lt_succ_of_le (Finset.le_max' A s0 hmem)
  exact lt_of_lt_of_le this hs'ge

/-- `greedySidon` is strictly monotone. -/
lemma greedySidon.strictMono : StrictMono greedySidon :=
  strictMono_nat_of_lt_succ greedySidon.lt_succ

/-- Hence `greedySidon` is injective. -/
lemma greedySidon.injective : Function.Injective greedySidon :=
  greedySidon.strictMono.injective

/-- Every term of the greedy Sidon sequence is at least `1`. -/
lemma one_le_greedySidon (n : ℕ) : 1 ≤ greedySidon n := by
  simpa [greedySidon_zero] using
    (greedySidon.strictMono.monotone (Nat.zero_le n) : greedySidon 0 ≤ greedySidon n)

/-- Index lower bound: `n ≤ greedySidon n` (via strict monotonicity on `ℕ`). -/
lemma le_greedySidon (n : ℕ) : n ≤ greedySidon n :=
  StrictMono.id_le greedySidon.strictMono n





/-- The finite Sidon set at step `n` is exactly `{greedySidon 0, …, greedySidon n}`. -/
lemma greedySidon.aux_eq_image (n : ℕ) :
    (greedySidon.aux n).1.1 = (Finset.range (n + 1)).image greedySidon := by
  induction n with
  | zero =>
    ext x
    simp [aux_zero, greedySidon_zero]
  | succ n ih =>
    have hunion :
        (greedySidon.aux (n + 1)).1.1 =
          (greedySidon.aux n).1.1 ∪ {greedySidon (n + 1)} := by
      dsimp [greedySidon.aux, greedySidon]
    have hnotin : greedySidon (n + 1) ∉ (Finset.range (n + 1)).image greedySidon := by
      intro h
      obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp h
      have hi' : i < n + 1 := mem_range.mp hi
      exact (hi'.ne (greedySidon.injective hgi)).elim
    ext x
    simp only [hunion, ih, mem_union, mem_image, mem_range, mem_singleton]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨n + 1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have : i ≤ n ∨ i = n + 1 := by omega
      cases this with
      | inl hle => exact Or.inl ⟨i, Nat.lt_succ_iff.mpr hle, rfl⟩
      | inr heq =>
        subst heq
        exact Or.inr rfl

/-- Membership in the finite greedy set ↔ some index `≤ n`. -/
lemma greedySidon.mem_aux_iff {n x : ℕ} :
    x ∈ (greedySidon.aux n).1.1 ↔ ∃ i ≤ n, greedySidon i = x := by
  constructor
  · intro hx
    rw [aux_eq_image, mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Nat.lt_succ_iff.mp (mem_range.mp hi), rfl⟩
  · rintro ⟨i, hle, rfl⟩
    rw [aux_eq_image, mem_image]
    exact ⟨i, mem_range.mpr (Nat.lt_succ_iff.mpr hle), rfl⟩

/-- Elements of the finite greedy set are at least `1`. -/
lemma one_le_of_mem_greedySidon_aux {n x : ℕ} (hx : x ∈ (greedySidon.aux n).1.1) :
    1 ≤ x := by
  obtain ⟨i, _, rfl⟩ := greedySidon.mem_aux_iff.mp hx
  exact one_le_greedySidon i

/-- `greedySidonBelow N` sits inside `{1, …, N}`. -/
lemma greedySidonBelow_subset_Icc (N : ℕ) : greedySidonBelow N ⊆ Icc 1 N := by
  intro x hx
  rw [mem_greedySidonBelow] at hx
  exact mem_Icc.mpr ⟨one_le_of_mem_greedySidon_aux hx.1, hx.2⟩

/-- Hence `#greedySidonBelow N ≤ N`. -/
lemma card_greedySidonBelow_le (N : ℕ) : (greedySidonBelow N).card ≤ N := by
  simpa [Nat.card_Icc] using card_le_card (greedySidonBelow_subset_Icc N)

/-- Membership in `greedySidonBelow` via the infinite sequence. -/
lemma mem_greedySidonBelow_iff_exists {N x : ℕ} :
    x ∈ greedySidonBelow N ↔ ∃ i : ℕ, greedySidon i = x ∧ x ≤ N := by
  constructor
  · intro hx
    obtain ⟨hmem, hle⟩ := mem_greedySidonBelow.mp hx
    obtain ⟨i, _, rfl⟩ := greedySidon.mem_aux_iff.mp hmem
    exact ⟨i, rfl, hle⟩
  · rintro ⟨i, rfl, hle⟩
    have hi : i ≤ N := (le_greedySidon i).trans hle
    exact mem_greedySidonBelow.mpr ⟨greedySidon.mem_aux_iff.mpr ⟨i, hi, rfl⟩, hle⟩

/-- In particular `greedySidonBelow` is empty precisely when `N = 0`. -/
lemma greedySidonBelow_eq_empty_iff (N : ℕ) :
    greedySidonBelow N = ∅ ↔ N = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hne
    have : (1 : ℕ) ∈ greedySidonBelow N := by
      refine mem_greedySidonBelow_iff_exists.mpr ⟨0, greedySidon_zero, ?_⟩
      simpa [greedySidon_zero] using hpos
    simp [h] at this
  · rintro rfl
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hx' := mem_greedySidonBelow.mp hx
    have : 1 ≤ x := one_le_of_mem_greedySidon_aux hx'.1
    omega

/-- The greedy Sidon set in `{1, …, N}` grows with `N`. -/
lemma greedySidonBelow_mono {M N : ℕ} (h : M ≤ N) :
    greedySidonBelow M ⊆ greedySidonBelow N := by
  intro x hx
  rw [mem_greedySidonBelow] at hx ⊢
  exact ⟨greedySidon.aux_mono h hx.1, hx.2.trans h⟩

/-- Hence `#greedySidonBelow` is monotone in `N`. -/
lemma card_greedySidonBelow_mono {M N : ℕ} (h : M ≤ N) :
    (greedySidonBelow M).card ≤ (greedySidonBelow N).card :=
  card_le_card (greedySidonBelow_mono h)

/-- `1` belongs to `greedySidonBelow N` precisely when `N ≥ 1`. -/
lemma one_mem_greedySidonBelow_iff (N : ℕ) :
    (1 : ℕ) ∈ greedySidonBelow N ↔ 1 ≤ N := by
  constructor
  · intro h
    exact (mem_greedySidonBelow.mp h).2
  · intro hN
    exact mem_greedySidonBelow_iff_exists.mpr
      ⟨0, greedySidon_zero, by simpa [greedySidon_zero] using hN⟩

/-- In particular `#greedySidonBelow N ≥ 1` for `N ≥ 1`. -/
lemma one_le_card_greedySidonBelow_of_one_le {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ (greedySidonBelow N).card :=
  card_pos.mpr ⟨1, (one_mem_greedySidonBelow_iff N).mpr hN⟩

/-- The greedy construction is a Sidon subset of `{1, …, N}`, so
`#greedySidonBelow N ≤ maxSidonSubsetCard (Icc 1 N)`. -/
lemma card_greedySidonBelow_le_maxSidonSubsetCard (N : ℕ) :
    (greedySidonBelow N).card ≤ maxSidonSubsetCard (Icc 1 N) :=
  card_le_maxSidonSubsetCard (greedySidonBelow_subset_Icc N) (greedySidonBelow_isSidon N)

/-- Consequently `2 ^ #greedySidonBelow N ≤ sidonSubsetCount (Icc 1 N)`. -/
lemma two_pow_card_greedySidonBelow_le_sidonSubsetCount (N : ℕ) :
    2 ^ (greedySidonBelow N).card ≤ sidonSubsetCount (Icc 1 N) :=
  two_pow_card_le_sidonSubsetCount_of_isSidon
    (greedySidonBelow_subset_Icc N) (greedySidonBelow_isSidon N)

/-- `#greedySidonBelow N = 0` precisely when `N = 0`. -/
lemma card_greedySidonBelow_eq_zero_iff (N : ℕ) :
    (greedySidonBelow N).card = 0 ↔ N = 0 := by
  rw [card_eq_zero, greedySidonBelow_eq_empty_iff]

/-- A greedy Sidon term lies in `greedySidonBelow N` iff it does not exceed `N`. -/
lemma greedySidon_mem_greedySidonBelow_iff {i N : ℕ} :
    greedySidon i ∈ greedySidonBelow N ↔ greedySidon i ≤ N := by
  constructor
  · intro h
    exact (mem_greedySidonBelow.mp h).2
  · intro hle
    exact mem_greedySidonBelow_iff_exists.mpr ⟨i, rfl, hle⟩

end Finset
