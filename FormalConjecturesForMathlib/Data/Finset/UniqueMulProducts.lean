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

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Image

@[expose] public section

namespace Finset

/-- The number of representations of `m` as `a * b` with `a ∈ A` and `b ∈ B`. -/
def mulRepresentationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  (A.product B).filter (fun p => p.1 * p.2 = m) |>.card

/-- The products `a * b` with `a ∈ A`, `b ∈ B` that have exactly one such representation. -/
def uniqueMulProducts (A B : Finset ℕ) : Finset ℕ :=
  ((A.product B).image (fun p => p.1 * p.2)).filter (fun m =>
    mulRepresentationCount A B m = 1)

@[simp]
lemma mulRepresentationCount_empty_left (B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount ∅ B m = 0 := by
  simp [mulRepresentationCount]

@[simp]
lemma uniqueMulProducts_empty_left (B : Finset ℕ) :
    uniqueMulProducts ∅ B = ∅ := by
  simp [uniqueMulProducts]

@[simp]
lemma mulRepresentationCount_empty_right (A : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A ∅ m = 0 := by
  simp [mulRepresentationCount]

@[simp]
lemma uniqueMulProducts_empty_right (A : Finset ℕ) :
    uniqueMulProducts A ∅ = ∅ := by
  simp [uniqueMulProducts]

lemma mulRepresentationCount_singleton (a b m : ℕ) :
    mulRepresentationCount {a} {b} m = if a * b = m then 1 else 0 := by
  simp [mulRepresentationCount, filter_singleton]
  split_ifs <;> simp

lemma uniqueMulProducts_singleton (a b : ℕ) :
    uniqueMulProducts {a} {b} = {a * b} := by
  simp [uniqueMulProducts, mulRepresentationCount_singleton]

lemma mulRepresentationCount_le_card (A B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A B m ≤ A.card * B.card := by
  simpa [mulRepresentationCount, card_product] using
    card_filter_le (A.product B) (fun p => p.1 * p.2 = m)

lemma uniqueMulProducts_subset_image (A B : Finset ℕ) :
    uniqueMulProducts A B ⊆ (A.product B).image (fun p => p.1 * p.2) :=
  filter_subset _ _

/-- There are at most `#A * #B` uniquely represented products. -/
lemma card_uniqueMulProducts_le (A B : Finset ℕ) :
    (uniqueMulProducts A B).card ≤ A.card * B.card := by
  calc
    (uniqueMulProducts A B).card
        ≤ ((A.product B).image fun p => p.1 * p.2).card :=
          card_le_card (uniqueMulProducts_subset_image A B)
    _ ≤ (A.product B).card := card_image_le
    _ = A.card * B.card := card_product A B

@[simp]
lemma mem_uniqueMulProducts {A B : Finset ℕ} {m : ℕ} :
    m ∈ uniqueMulProducts A B ↔
      m ∈ (A.product B).image (fun p => p.1 * p.2) ∧ mulRepresentationCount A B m = 1 := by
  simp [uniqueMulProducts]

lemma mulRepresentationCount_eq_zero_iff (A B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A B m = 0 ↔ ∀ a ∈ A, ∀ b ∈ B, a * b ≠ m := by
  classical
  simp [mulRepresentationCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_product]
  constructor <;> intro h <;> intros <;> apply h <;> assumption

lemma mulRepresentationCount_pos_iff (A B : Finset ℕ) (m : ℕ) :
    0 < mulRepresentationCount A B m ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = m := by
  simp [Nat.pos_iff_ne_zero, mulRepresentationCount_eq_zero_iff]

/-- Swapping factors does not change representation counts (`ℕ` multiplication is commutative). -/
lemma mulRepresentationCount_comm (A B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A B m = mulRepresentationCount B A m := by
  classical
  simp only [mulRepresentationCount, product_eq_sprod]
  refine card_bij (fun p _ ↦ (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [mul_comm]; exact hp.2⟩
  · intro p₁ _ p₂ _ h
    cases p₁; cases p₂; simp_all
  · intro q hq
    rw [mem_filter, mem_product] at hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    rw [mem_filter, mem_product]
    exact ⟨⟨hq.1.2, hq.1.1⟩, by rw [mul_comm]; exact hq.2⟩

lemma image_mul_product_comm (A B : Finset ℕ) :
    (A.product B).image (fun p ↦ p.1 * p.2) = (B.product A).image (fun p ↦ p.1 * p.2) := by
  simp only [product_eq_sprod]
  ext m
  simp only [mem_image, mem_product]
  constructor <;> rintro ⟨p, ⟨hp₁, hp₂⟩, rfl⟩
  · exact ⟨(p.2, p.1), ⟨hp₂, hp₁⟩, (mul_comm _ _).symm⟩
  · exact ⟨(p.2, p.1), ⟨hp₂, hp₁⟩, (mul_comm _ _).symm⟩

lemma uniqueMulProducts_comm (A B : Finset ℕ) :
    uniqueMulProducts A B = uniqueMulProducts B A := by
  ext m
  constructor
  · intro h
    rw [mem_uniqueMulProducts] at h ⊢
    exact ⟨(image_mul_product_comm A B ▸ h.1), (mulRepresentationCount_comm A B m ▸ h.2)⟩
  · intro h
    rw [mem_uniqueMulProducts] at h ⊢
    exact ⟨(image_mul_product_comm A B).symm ▸ h.1, (mulRepresentationCount_comm A B m).symm ▸ h.2⟩

lemma mulRepresentationCount_mono_left {A A' : Finset ℕ} (h : A ⊆ A') (B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A B m ≤ mulRepresentationCount A' B m := by
  classical
  simpa [mulRepresentationCount, product_eq_sprod] using
    card_le_card (filter_subset_filter (fun p : ℕ × ℕ ↦ p.1 * p.2 = m)
      (product_subset_product_left (s := A) (s' := A') (t := B) h))

lemma mulRepresentationCount_mono_right (A : Finset ℕ) {B B' : Finset ℕ} (h : B ⊆ B') (m : ℕ) :
    mulRepresentationCount A B m ≤ mulRepresentationCount A B' m := by
  classical
  simpa [mulRepresentationCount, product_eq_sprod] using
    card_le_card (filter_subset_filter (fun p : ℕ × ℕ ↦ p.1 * p.2 = m)
      (product_subset_product_right (s := A) (t := B) (t' := B') h))

end Finset
