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
  simp [hY, this.1, setOf_and] at hY_card
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

/-- Ordered-pair characterisation of the Sidon property for a `Finset ℕ`: the coercion
`(A : Set ℕ)` is Sidon iff for all pairs `(a₁, b₁), (a₂, b₂)` of elements of `A` with
`a₁ ≤ b₁` and `a₂ ≤ b₂`, the equation `a₁ + b₁ = a₂ + b₂` forces `a₁ = a₂` and `b₁ = b₂`.
This ordered form is often more convenient than the up-to-commutativity disjunction in
`IsSidon` for counting arguments. -/
theorem isSidon_coe_iff (A : Finset ℕ) :
    IsSidon ((A : Set ℕ)) ↔
      ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ a₂ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + b₁ = a₂ + b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · -- IsSidon → ordered form. IsSidon's signature is (i₁, j₁, i₂, j₂) with sum
    -- i₁ + i₂ = j₁ + j₂. We have the ordered hsum : a₁ + b₁ = a₂ + b₂, so we
    -- map i₁=a₁, j₁=a₂, i₂=b₁, j₂=b₂ to align the sums.
    intro hS a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hab₁ hab₂ hsum
    have h_mem_a₁ : a₁ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr ha₁
    have h_mem_b₁ : b₁ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr hb₁
    have h_mem_a₂ : a₂ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr ha₂
    have h_mem_b₂ : b₂ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr hb₂
    have h_disj := hS a₁ h_mem_a₁ a₂ h_mem_a₂ b₁ h_mem_b₁ b₂ h_mem_b₂ hsum
    -- h_disj : (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂)
    cases h_disj with
    | inl h => exact h
    | inr h =>
      -- Case: a₁ = b₂, b₁ = a₂. With a₁ ≤ b₁ and a₂ ≤ b₂ this forces all four
      -- values equal, so the conclusion still holds.
      obtain ⟨ha, hb⟩ := h
      refine ⟨?_, ?_⟩ <;> omega
  · -- ordered form → IsSidon. Sort each pair to invoke the ordered hypothesis.
    intro hS i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    rw [Finset.mem_coe] at hi₁ hj₁ hi₂ hj₂
    by_cases h₁ : i₁ ≤ i₂
    · by_cases h₂ : j₁ ≤ j₂
      · have := hS i₁ hi₁ i₂ hi₂ j₁ hj₁ j₂ hj₂ h₁ h₂ hsum
        exact Or.inl ⟨this.1, this.2⟩
      · push_neg at h₂
        have h₂' : j₂ ≤ j₁ := Nat.le_of_lt h₂
        have hsum' : i₁ + i₂ = j₂ + j₁ := by omega
        have := hS i₁ hi₁ i₂ hi₂ j₂ hj₂ j₁ hj₁ h₁ h₂' hsum'
        exact Or.inr ⟨this.1, this.2⟩
    · push_neg at h₁
      have h₁' : i₂ ≤ i₁ := Nat.le_of_lt h₁
      by_cases h₂ : j₁ ≤ j₂
      · have hsum' : i₂ + i₁ = j₁ + j₂ := by omega
        have := hS i₂ hi₂ i₁ hi₁ j₁ hj₁ j₂ hj₂ h₁' h₂ hsum'
        exact Or.inr ⟨this.2, this.1⟩
      · push_neg at h₂
        have h₂' : j₂ ≤ j₁ := Nat.le_of_lt h₂
        have hsum' : i₂ + i₁ = j₂ + j₁ := by omega
        have := hS i₂ hi₂ i₁ hi₁ j₂ hj₂ j₁ hj₁ h₁' h₂' hsum'
        exact Or.inl ⟨this.2, this.1⟩

/-- In a Sidon set, a positive common difference determines its endpoints: if
`a₁ - b₁ = a₂ - b₂` with `b₁ < a₁` and `b₂ < a₂`, then `a₁ = a₂` and `b₁ = b₂`. -/
theorem sidon_diff_injective {A : Finset ℕ} (hS : IsSidon ((A : Set ℕ)))
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hlt₁ : b₁ < a₁) (hlt₂ : b₂ < a₂) (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  rw [isSidon_coe_iff] at hS
  by_cases h1 : b₂ ≤ a₁
  · by_cases h2 : b₁ ≤ a₂
    · have h_sidon := hS b₂ hb₂ a₁ ha₁ b₁ hb₁ a₂ ha₂ h1 h2 (by omega)
      exact ⟨h_sidon.right, h_sidon.left.symm⟩
    · push_neg at h2
      have h_sidon := hS b₂ hb₂ a₁ ha₁ a₂ ha₂ b₁ hb₁ h1 (Nat.le_of_lt h2) (by omega)
      exact absurd h_sidon.right.symm (Nat.ne_of_lt hlt₁)
  · push_neg at h1
    by_cases h2 : b₁ ≤ a₂
    · have h_sidon := hS a₁ ha₁ b₂ hb₂ b₁ hb₁ a₂ ha₂ (Nat.le_of_lt h1) h2 (by omega)
      exact absurd h_sidon.left.symm (Nat.ne_of_lt hlt₁)
    · push_neg at h2
      have h_sidon := hS a₁ ha₁ b₂ hb₂ a₂ ha₂ b₁ hb₁ (Nat.le_of_lt h1)
        (Nat.le_of_lt h2) (by omega)
      exact ⟨h_sidon.left, h_sidon.right.symm⟩

/-- For a finite set of naturals, twice the number of strictly increasing pairs
`(a, b) ∈ A ×ˢ A` (those with `a < b`) equals `|A| * (|A| - 1)`: each unordered pair of
distinct elements is counted exactly once. -/
theorem two_mul_card_product_filter_lt (A : Finset ℕ) :
    2 * ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = A.card * (A.card - 1) := by
  have h_filter_eq : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) =
      A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    constructor
    · intro ⟨⟨ha, hb⟩, hab⟩; exact ⟨⟨ha, hb, Nat.ne_of_lt hab⟩, hab⟩
    · intro ⟨⟨ha, hb, _⟩, hab⟩; exact ⟨⟨ha, hb⟩, hab⟩
  rw [h_filter_eq]
  have h_union : A.offDiag =
      A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
      A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨ha, hb, hab⟩
      rcases lt_or_gt_of_ne hab with h | h
      · exact Or.inl ⟨⟨ha, hb, hab⟩, h⟩
      · exact Or.inr ⟨⟨ha, hb, hab⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have h_disj : Disjoint
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2))
      (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)) :=
    Finset.disjoint_filter.mpr
      (fun ⟨_a, _b⟩ _ h1 h2 => absurd h1 (not_lt.mpr (le_of_lt h2)))
  have h_swap : (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card :=
    Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1))
      (fun ⟨_a, _b⟩ h => by
        simp only [Finset.mem_filter, Finset.mem_offDiag] at h ⊢
        exact ⟨⟨h.1.2.1, h.1.1, Ne.symm h.1.2.2⟩, h.2⟩)
      (fun ⟨_a, _b⟩ h => by
        simp only [Finset.mem_filter, Finset.mem_offDiag] at h ⊢
        exact ⟨⟨h.1.2.1, h.1.1, Ne.symm h.1.2.2⟩, h.2⟩)
      (fun _ _ => rfl) (fun _ _ => rfl)
  have h_card : A.offDiag.card =
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card +
      (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)).card := by
    rw [← Finset.card_union_of_disjoint h_disj, ← h_union]
  have h_mul_sub : A.card * (A.card - 1) = A.card * A.card - A.card := by
    cases A.card with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [show (n + 1) * (n + 1) = (n + 1) * n + (n + 1) from by ring, Nat.add_sub_cancel]
  have h_offDiag_eq : A.offDiag.card = A.card * (A.card - 1) :=
    A.offDiag_card.trans h_mul_sub.symm
  omega

/-- The strict lower-triangle companion of `Finset.two_mul_card_product_filter_lt`: twice the
number of strictly decreasing pairs `(a, b) ∈ A ×ˢ A` (those with `b < a`) equals
`|A| * (|A| - 1)`. -/
theorem two_mul_card_product_filter_gt (A : Finset ℕ) :
    2 * ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card = A.card * (A.card - 1) := by
  have h_swap : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · rintro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · rintro ⟨a, b⟩ _; rfl
    · rintro ⟨a, b⟩ _; rfl
  rw [h_swap, two_mul_card_product_filter_lt]

/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

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
