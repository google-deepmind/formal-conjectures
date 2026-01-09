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

import Mathlib.Order.Filter.AtTopBot.Finset

open Filter

theorem Finset.tendsto_card_atTop {α : Type*} [Infinite α] :
    atTop.Tendsto (Finset.card (α := α)) atTop := by
  classical
  apply tendsto_atTop_atTop_of_monotone Finset.card_mono fun n ↦ ?_
  obtain ⟨S, hS⟩ := (Set.infinite_univ (α := α)).exists_subset_card_eq n
  obtain ⟨g, hg⟩ := (Set.infinite_univ (α := α)).exists_notMem_finset S
  exact ⟨{g} ∪ S, by simp [Finset.card_insert_of_notMem hg.2, hS.2]⟩
