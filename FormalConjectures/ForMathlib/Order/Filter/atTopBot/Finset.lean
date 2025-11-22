import Mathlib.Order.Filter.AtTopBot.Finset

open Filter

theorem Finset.tendsto_card_atTop {α : Type*} [Infinite α] :
    atTop.Tendsto (Finset.card (α := α)) atTop := by
  classical
  apply tendsto_atTop_atTop_of_monotone Finset.card_mono fun n ↦ ?_
  obtain ⟨S, hS⟩ := (Set.infinite_univ (α := α)).exists_subset_card_eq n
  obtain ⟨g, hg⟩ := (Set.infinite_univ (α := α)).exists_notMem_finset S
  exact ⟨{g} ∪ S, by simp [Finset.card_insert_of_notMem hg.2, hS.2]⟩
