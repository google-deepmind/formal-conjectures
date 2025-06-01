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

import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Set.Card

theorem Finset.Iio_eventually_nonempty (β : Type*) [PartialOrder β] [LocallyFiniteOrder β]
    [OrderBot β] [Nontrivial β] : ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).Nonempty :=
  let ⟨b, hb⟩ := exists_ne (⊥ : β)
  ⟨b, fun n hn => by simp [ne_bot_of_le_ne_bot hb hn]⟩

theorem Finset.Iio_eventually_card_ne_zero (β : Type*) [PartialOrder β]
    [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).card ≠ 0 :=
  let ⟨b, hb⟩ := Iio_eventually_nonempty β
  ⟨b, fun n hn => by simp [nonempty_iff_ne_empty.1 <| hb n hn]⟩

theorem Set.Iio_eventually_ncard_ne_zero (β : Type*) [PartialOrder β]
    [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    ∃ (b : β), ∀ n ≥ b, (Set.Iio n).ncard ≠ 0 :=
  let ⟨b, hb⟩ := Finset.Iio_eventually_card_ne_zero β
  ⟨b, fun n hn => by rw [← Finset.coe_Iio, Set.ncard_coe_Finset]; exact hb n hn⟩
