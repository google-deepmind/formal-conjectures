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
import Mathlib.Data.Finset.Card

namespace Finset
variable {α : Type*} {s t : Finset α}

lemma card_le_card_iff_of_subset (hst : s ⊆ t) : #t ≤ #s ↔ s = t where
  mp := eq_of_subset_of_card_le hst
  mpr := by rintro rfl; rfl

lemma card_lt_card_iff_of_subset (hst : s ⊆ t) : #s < #t ↔ s ≠ t := by
  rw [← not_le, card_le_card_iff_of_subset hst]

end Finset
