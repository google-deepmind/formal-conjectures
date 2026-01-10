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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 949

*Reference:* [erdosproblems.com/949](https://www.erdosproblems.com/949)
-/

open Cardinal Filter
open scoped Pointwise Topology


namespace Erdos949

/--
Let $S \subseteq \mathbb{R}$ be a set containing no solutions to $a + b = c$.
Must there be a set $A \subseteq \mathbb{R} \setminus S$ of cardinality continuum such that
$A + A \subseteq \mathbb{R}\setminus S$?
-/
@[category research open, AMS 5]
theorem erdos_949 : answer(sorry) ↔
    ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ :=
  sorry

/-- Let $S\sub \mathbb{R}$ be a Sidon set. Must there be a set $A\sub \mathbb{R}∖S$ of cardinality
continuum such that $A + A \sub \mathbb{R}∖S$? -/
@[category research solved, AMS 5]
theorem erdos_949.variants.sidon : answer(True) ↔
    ∀ S : Set ℝ, IsSidon S → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  simp only [true_iff, Set.add_subset_iff]
  rintro S hS
  -- We case on whether `S` has cardinality the continuum or strictly less.
  obtain hS𝔠 | hS𝔠 : #S < 𝔠 ∨ #S = 𝔠 := lt_or_eq_of_le <| by simpa using mk_set_le S
  -- If `S` has cardinality strictly less than the continuum, then we pick by Zorn `A` maximal
  -- such that both `A` and `A + A` are disjoint from `S`.
  · obtain ⟨A, ⟨hAS, hAAS⟩, hAmax⟩ := by
      refine zorn_subset {A ⊆ Sᶜ | ∀ x ∈ A,∀ y ∈ A, x + y ∉ S} ?_
      simp only [Set.setOf_and, Set.subset_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp,
        and_assoc]
      refine fun C hCS hSC hC ↦ ⟨_, Set.iUnion₂_subset hCS, ?_, Set.subset_iUnion₂⟩
      simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
      rintro x A hA hx y B hB hy
      obtain ⟨D, hD, hAD, hBD⟩ := hC.directedOn _ hA _ hB
      exact hSC hD _ (hAD hx) _ (hBD hy)
    -- By construction, `A` satisfies all properties except possibly for having size the continuum.
    refine ⟨A, hAS, ?_, hAAS⟩
    -- By maximality, `Sᶜ ∩ (S / 2)ᶜ ⊆ A ∪ ⋃ a ∈ A, (S - a)`.
    replace hAmax : Sᶜ ∩ ((· / 2) '' S)ᶜ ⊆ A ∪ ⋃ a ∈ A, (· - a) '' S
    · simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_eq_iff_mul_eq, mul_two, exists_eq_right',
      Set.mem_union, Set.mem_iUnion, sub_eq_iff_eq_add, exists_eq_right, exists_prop,
      or_iff_not_imp_left, and_imp]
      rintro x hxS hxxS hxA
      by_contra! hxAS
      refine hxA <| hAmax ?_ (Set.subset_insert ..) (Set.mem_insert ..)
      simpa [Set.insert_subset_iff, forall_and, add_comm _ x, *] using ⟨hxAS, hAAS⟩
    -- By assumption, `#(Sᶜ ∩ (S / 2)ᶜ) = 𝔠`.
    have hS𝔠' : #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) = 𝔠
    · rw [← Set.compl_union, mk_compl_of_infinite, mk_real]
      grw [mk_union_le, Cardinal.mk_real]
      refine add_lt_of_lt aleph0_le_continuum hS𝔠 ?_
      grw [mk_image_le]
      exact hS𝔠
    -- If `#A < 𝔠`, we would then have
    -- `𝔠 = #(Sᶜ ∩ (S / 2)ᶜ) ≤ #(A ∪ ⋃ a ∈ A, (S - a)) ≤ #A + #A * #S < 𝔠`, contradiction.
    refine (mk_real ▸ mk_set_le _).eq_of_not_lt fun hA𝔠 ↦ lt_irrefl 𝔠 ?_
    calc
      𝔠 = #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) := by rw [hS𝔠']
      _ ≤ #↑(A ∪ ⋃ a ∈ A, (· - a) '' S) := mk_subtype_mono hAmax
      _ ≤ #A + #A * #S := by
        obtain rfl | hA := A.eq_empty_or_nonempty
        · simp
        have : Nonempty A := hA.coe_sort
        grw [mk_union_le, mk_biUnion_le, ciSup_le fun _ ↦ mk_image_le]
      _ < 𝔠 := add_lt_of_lt aleph0_le_continuum hA𝔠 <| mul_lt_of_lt aleph0_le_continuum hA𝔠 hS𝔠
  -- If `S` has cardinality the continuum, then we pick some `a ≠ 0` in `S` and set
  -- `A := (S \ {a} - a / 2) \ S`.
  have hSinf : S.Infinite := by simpa using aleph0_le_continuum.trans_eq hS𝔠.symm
  obtain ⟨a, ha, ha₀⟩ : ∃ a ∈ S, a ≠ 0 := (hSinf.diff <| Set.finite_singleton 0).nonempty
  refine ⟨(· - a / 2) '' (S \ {a}) \ S, Set.diff_subset_compl .., ?_, ?_⟩
  -- Since `S` is Sidon and `a ≠ 0`, `(S - a / 2) ∩ S ⊇ (S \ {a} - a / 2) ∩ S` has at most one
  -- element. In particular, `#A = #(S \ {a} - a / 2) = #S = 𝔠` as wanted.
  · rw [mk_diff_eq_left_of_finite' ((hSinf.diff <| Set.finite_singleton _).image
      sub_left_injective.injOn)]
    · simp [Cardinal.mk_image_eq sub_left_injective, *]
    · refine Set.Subsingleton.finite ?_
      rintro _ ⟨⟨x, ⟨hx, -⟩, rfl⟩, hxa⟩ _ ⟨⟨y, ⟨hy, -⟩, rfl⟩, hya⟩
      obtain rfl : x = y := by
        simpa [ha₀, eq_comm (b := x - _)] using hS _ hya _ hxa _ hx _ hy (by ring)
      rfl
  -- Since `S` is Sidon, `S \ {a} + S \ {a} - a ⊇ A + A` is disjoint from `S`, as wanted.
  · rintro _ ⟨⟨x, ⟨hx, hxa⟩, rfl⟩, -⟩ _ ⟨⟨y, ⟨hy, hya⟩, rfl⟩, -⟩ hxy
    have := hS _ hx _ ha _ hy _ hxy (by ring)
    simp_all

end Erdos949
