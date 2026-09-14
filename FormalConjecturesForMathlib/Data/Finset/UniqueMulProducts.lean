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

@[simp]
lemma card_uniqueMulProducts_comm (A B : Finset ℕ) :
    (uniqueMulProducts A B).card = (uniqueMulProducts B A).card := by
  rw [uniqueMulProducts_comm]

/-- `mulRepresentationCount = 1` means there is a unique factor pair in `A × B`. -/
lemma mulRepresentationCount_eq_one_iff (A B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A B m = 1 ↔
      ∃! p : ℕ × ℕ, p ∈ A.product B ∧ p.1 * p.2 = m := by
  classical
  rw [mulRepresentationCount, Finset.card_eq_one]
  constructor
  · rintro ⟨p, hp⟩
    have hpmem : p ∈ (A.product B).filter (fun r => r.1 * r.2 = m) := by
      rw [hp]; exact mem_singleton_self _
    have hp' := mem_filter.mp hpmem
    refine ⟨p, ⟨hp'.1, hp'.2⟩, fun q hq => ?_⟩
    have hq' : q ∈ (A.product B).filter (fun r => r.1 * r.2 = m) :=
      mem_filter.mpr ⟨hq.1, hq.2⟩
    exact mem_singleton.mp (hp ▸ hq')
  · rintro ⟨p, ⟨hpA, hpm⟩, huniq⟩
    refine ⟨p, ?_⟩
    ext q
    simp only [mem_filter, mem_singleton]
    exact ⟨fun ⟨hqA, hqm⟩ => huniq q ⟨hqA, hqm⟩,
      fun h => h ▸ ⟨hpA, hpm⟩⟩

/-- Membership in `uniqueMulProducts` is equivalent to a unique factorisation in `A × B`. -/
lemma mem_uniqueMulProducts_iff_existsUnique {A B : Finset ℕ} {m : ℕ} :
    m ∈ uniqueMulProducts A B ↔ ∃! p : ℕ × ℕ, p ∈ A.product B ∧ p.1 * p.2 = m := by
  classical
  constructor
  · intro hm
    rw [mem_uniqueMulProducts] at hm
    exact (mulRepresentationCount_eq_one_iff A B m).mp hm.2
  · intro h
    refine mem_uniqueMulProducts.mpr ⟨?_, (mulRepresentationCount_eq_one_iff A B m).mpr h⟩
    obtain ⟨p, ⟨hpA, hpm⟩, _⟩ := h
    exact mem_image.mpr ⟨p, hpA, hpm⟩

/-- If `A, B ⊆ S`, then there are at most `(#S)²` uniquely represented products. -/
lemma card_uniqueMulProducts_le_sq_of_subset {A B S : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) :
    (uniqueMulProducts A B).card ≤ S.card ^ 2 := by
  simpa [sq] using
    (card_uniqueMulProducts_le A B).trans
      (Nat.mul_le_mul (card_le_card hA) (card_le_card hB))


/-- With a single nonzero left factor, each attainable product has representation count `1`. -/
lemma mulRepresentationCount_singleton_left (a : ℕ) (B : Finset ℕ) (m : ℕ)
    (ha : a ≠ 0) :
    mulRepresentationCount {a} B m = if ∃ b ∈ B, a * b = m then 1 else 0 := by
  classical
  by_cases h : ∃ b ∈ B, a * b = m
  · obtain ⟨b, hb, rfl⟩ := h
    rw [if_pos ⟨b, hb, rfl⟩, mulRepresentationCount, card_eq_one]
    refine ⟨(a, b), Finset.ext fun p => ?_⟩
    constructor
    · intro hp
      have hp' := mem_filter.mp hp
      have ha' : p.1 = a := mem_singleton.mp (mem_product.mp hp'.1).1
      have heq : a * p.2 = a * b := by
        convert hp'.2
        exact ha'.symm
      have hb' : p.2 = b := Nat.mul_left_cancel (Nat.pos_of_ne_zero ha) heq
      exact mem_singleton.mpr (Prod.ext ha' hb')
    · intro hp
      rw [mem_singleton.mp hp]
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_singleton_self a, hb⟩, rfl⟩
  · rw [if_neg h, mulRepresentationCount_eq_zero_iff]
    intro x hx y hy hxy
    exact h ⟨y, hy, by simpa [mem_singleton.mp hx] using hxy⟩

/-- Nonzero left singleton: uniquely represented products are exactly `{a} · B`. -/
lemma uniqueMulProducts_singleton_left (a : ℕ) (B : Finset ℕ) (ha : a ≠ 0) :
    uniqueMulProducts {a} B = B.image (fun b => a * b) := by
  classical
  ext m
  constructor
  · intro hm
    have him := (mem_uniqueMulProducts.mp hm).1
    obtain ⟨p, hp, rfl⟩ := mem_image.mp him
    have hpA := (mem_product.mp hp).1
    have hpB := (mem_product.mp hp).2
    have ha' : p.1 = a := mem_singleton.mp hpA
    exact mem_image.mpr ⟨p.2, hpB, by rw [ha']⟩
  · intro hm
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hm
    refine mem_uniqueMulProducts.mpr ⟨?_, ?_⟩
    · exact mem_image.mpr ⟨(a, b), mem_product.mpr ⟨mem_singleton_self a, hb⟩, rfl⟩
    · rw [mulRepresentationCount_singleton_left a B (a * b) ha, if_pos ⟨b, hb, rfl⟩]

/-- Left multiplication by nonzero `a` is injective. -/
lemma mul_left_injective_nat {a : ℕ} (ha : a ≠ 0) :
    Function.Injective fun b : ℕ => a * b :=
  fun _ _ h => Nat.mul_left_cancel (Nat.pos_of_ne_zero ha) h

/-- Right multiplication by nonzero `b` is injective. -/
lemma mul_right_injective_nat {b : ℕ} (hb : b ≠ 0) :
    Function.Injective fun a : ℕ => a * b :=
  fun _ _ h => Nat.mul_right_cancel (Nat.pos_of_ne_zero hb) h

/-- Hence `# uniqueMulProducts {a} B = #B` when `a ≠ 0`. -/
lemma card_uniqueMulProducts_singleton_left (a : ℕ) (B : Finset ℕ) (ha : a ≠ 0) :
    (uniqueMulProducts {a} B).card = B.card := by
  rw [uniqueMulProducts_singleton_left a B ha]
  exact card_image_of_injective _ (mul_left_injective_nat ha)

/-- Symmetric: nonzero right singleton. -/
lemma uniqueMulProducts_singleton_right (A : Finset ℕ) (b : ℕ) (hb : b ≠ 0) :
    uniqueMulProducts A {b} = A.image (fun a => a * b) := by
  rw [uniqueMulProducts_comm, uniqueMulProducts_singleton_left b A hb]
  simp [mul_comm]

lemma card_uniqueMulProducts_singleton_right (A : Finset ℕ) (b : ℕ) (hb : b ≠ 0) :
    (uniqueMulProducts A {b}).card = A.card := by
  rw [uniqueMulProducts_singleton_right A b hb]
  exact card_image_of_injective _ (mul_right_injective_nat hb)



/-- Left factor `0`: products are `0` with multiplicity `#B`, and nothing else. -/
lemma mulRepresentationCount_zero_left (B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount {0} B m = if m = 0 then B.card else 0 := by
  classical
  by_cases hm : m = 0
  · subst hm
    change (({0} ×ˢ B).filter fun p => p.1 * p.2 = 0).card = B.card
    have hself : (({0} ×ˢ B).filter fun p => p.1 * p.2 = 0) = {0} ×ˢ B :=
      filter_eq_self.mpr fun p hp => by
        have hp0 : p.1 = 0 := (mem_product.mp hp).1 |> mem_singleton.mp
        simp [hp0]
    rw [hself, card_product, card_singleton, one_mul]
  · rw [if_neg hm]
    exact (mulRepresentationCount_eq_zero_iff _ _ _).mpr fun a ha b _hb hprod => by
      have ha0 : a = 0 := mem_singleton.mp ha
      simp [ha0] at hprod
      exact hm hprod.symm

/-- Symmetrically for right factor `0`. -/
lemma mulRepresentationCount_zero_right (A : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A {0} m = if m = 0 then A.card else 0 := by
  rw [mulRepresentationCount_comm, mulRepresentationCount_zero_left]

/-- Unique products with left `{0}`: `{0}` iff `#B = 1`, otherwise empty. -/
lemma uniqueMulProducts_zero_left (B : Finset ℕ) :
    uniqueMulProducts {0} B = if B.card = 1 then ({0} : Finset ℕ) else ∅ := by
  classical
  split_ifs with hB
  · ext m
    simp only [mem_uniqueMulProducts, mulRepresentationCount_zero_left, hB, mem_singleton]
    constructor
    · rintro ⟨_him, hcnt⟩
      by_contra hm
      simp [hm] at hcnt
    · intro hm
      subst hm
      obtain ⟨b, rfl⟩ := card_eq_one.mp hB
      refine ⟨mem_image.mpr ⟨(0, b), by simp, by simp⟩, by simp⟩
  · ext m
    simp only [mem_uniqueMulProducts, mulRepresentationCount_zero_left]
    constructor
    · rintro ⟨_him, hcnt⟩
      by_cases hm : m = 0
      · subst hm; simp [hB] at hcnt
      · simp [hm] at hcnt
    · intro hmem
      exact absurd hmem (notMem_empty m)

/-- Symmetrically for right `{0}`. -/
lemma uniqueMulProducts_zero_right (A : Finset ℕ) :
    uniqueMulProducts A {0} = if A.card = 1 then ({0} : Finset ℕ) else ∅ := by
  rw [uniqueMulProducts_comm, uniqueMulProducts_zero_left]

@[simp]
lemma card_uniqueMulProducts_zero_left (B : Finset ℕ) :
    (uniqueMulProducts {0} B).card = if B.card = 1 then 1 else 0 := by
  rw [uniqueMulProducts_zero_left]
  split_ifs <;> simp

@[simp]
lemma card_uniqueMulProducts_zero_right (A : Finset ℕ) :
    (uniqueMulProducts A {0}).card = if A.card = 1 then 1 else 0 := by
  rw [uniqueMulProducts_zero_right]
  split_ifs <;> simp

end Finset
