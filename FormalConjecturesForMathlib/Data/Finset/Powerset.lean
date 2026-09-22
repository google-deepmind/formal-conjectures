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

public import Mathlib.Data.Finset.Powerset

public section

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α} {n : ℕ}

/-- The `(#t + 1)`-subsets of `s` that contain `t ⊆ s` are exactly the sets `insert a t` with
`a ∈ s \ t`. -/
lemma filter_subset_powersetCard_card_add_one (h : t ⊆ s) :
    (powersetCard (#t + 1) s).filter (t ⊆ ·) = (s \ t).image (insert · t) := by
  ext u
  simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
  constructor
  · rintro ⟨⟨hus, hu⟩, htu⟩
    have h1 : #(u \ t) = 1 := by rw [card_sdiff_of_subset htu, hu]; omega
    obtain ⟨a, ha⟩ := card_eq_one.1 h1
    have hat : a ∈ u \ t := by rw [ha]; exact mem_singleton_self a
    rw [mem_sdiff] at hat
    refine ⟨a, ⟨hus hat.1, hat.2⟩, ?_⟩
    rw [insert_eq, ← ha, sdiff_union_of_subset htu]
  · rintro ⟨a, ⟨has, hat⟩, rfl⟩
    exact ⟨⟨insert_subset has h, card_insert_of_notMem hat⟩, subset_insert _ _⟩

/-- A `k`-subset `t` of `s` lies in exactly `#s - k` of the `(k + 1)`-subsets of `s`. -/
lemma card_filter_subset_powersetCard_card_add_one (h : t ⊆ s) :
    #((powersetCard (#t + 1) s).filter (t ⊆ ·)) = #s - #t := by
  rw [filter_subset_powersetCard_card_add_one h, card_image_of_injOn, card_sdiff_of_subset h]
  intro a ha b _ hab
  have : a ∈ insert b t := by
    rw [← show insert a t = insert b t from hab]
    exact mem_insert_self a t
  rw [mem_insert] at this
  exact this.resolve_right (mem_sdiff.1 ha).2

end Finset
