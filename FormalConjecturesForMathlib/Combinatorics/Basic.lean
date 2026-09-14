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

lemma IsSidon.singleton (a : α) : IsSidon ({a} : Set α) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  subst hi₁; subst hj₁; subst hi₂; subst hj₂
  exact Or.inl ⟨rfl, rfl⟩

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
      simp [heq]; exact mem_powerset_self A
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

end Finset
