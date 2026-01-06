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
@[category research open, AMS 5]
theorem erdos_949.variants.sidon : answer(True) ↔
    ∀ S : Set ℝ, IsSidon S → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  field_simp only [true_iff,Set.add_subset_iff,IsSidon]
  use fun R L=> if a:Cardinal.mk R=.continuum then(? _)else(? _)
  · rcases R.eq_empty_or_nonempty with a| ⟨a, _⟩
    · use R,by bound,by valid, a▸nofun
    by_cases h:Cardinal.mk {M ∈R|M≠a}≥.continuum
    · by_cases h:Cardinal.mk {S ∈R | S≠a}=.continuum
      · by_cases h:Cardinal.mk ↑({S ∈R | S≠a}.image (.-a/2)) =.continuum
        · obtain ⟨rfl⟩ :=eq_or_ne a 0
          · let U := { a ∈R|a≠0}
            rcases U.eq_empty_or_nonempty with a| ⟨a, H, _⟩
            · simp_all[U,Cardinal.continuum_ne_zero.symm]
              cases Cardinal.continuum_ne_zero (h▸Cardinal.mk_eq_zero_iff.2 ⟨(·.2.symm.elim (mt (a _) ) )⟩)
            by_cases h:Cardinal.mk ↑(U\{a})=.continuum
            · by_cases h:Cardinal.mk ((U\{a}).image (.-a/2)) =.continuum
              · by_contra!
                specialize this ((.-a/2) '' (U\{a})\R) _ _
                · exact Set.diff_subset_compl _ _
                · have:=((.-a/2) '' (U\singleton a)).diff_union_inter R▸Cardinal.mk_union_le _ _
                  use le_antisymm (Cardinal.mk_real▸Cardinal.mk_set_le _) (not_lt.1 fun and=>this.not_lt (h▸Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum and ?_))
                  apply lt_of_le_of_lt
                  show _ ≤ 1
                  · refine Cardinal.le_one_iff_subsingleton.2 ⟨fun⟨ _,⟨A, B, rfl⟩,M⟩⟨ _,⟨D,E, rfl⟩,F⟩=>Subtype.eq ?_⟩
                    use (by_contra (by bound[(L _) M _ F D E.1.1 A B.1.1 (by ring)]))
                  exact (Cardinal.nat_lt_continuum _)
                obtain ⟨x,⟨⟨y,@c, rfl⟩, _⟩,z,⟨⟨z,@c, rfl⟩, _⟩, _⟩:=this
                bound[L y (And.left (by assumption)) a H z c.1 (@y-a/2+ (@ z-a/2)) (by_contra ‹_›  ) (by·ring),‹ y≠ a›.symm, true,‹z≠ a›.symm]
              rcases (h (by rwa [Cardinal.mk_image_eq_of_injOn _ _ sub_left_injective.injOn]))
            have:=U.diff_union_of_subset (Set.singleton_subset_iff.2<|by use H)▸Cardinal.mk_union_le ..
            cases(this.not_lt) (Cardinal.mk_singleton a▸by convert Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum ((Cardinal.mk_real▸Cardinal.mk_set_le _).lt_of_ne h) (Cardinal.nat_lt_continuum 1))
          use(.-a/2) ''{S ∈R | S≠a} \R
          use fun and=>by norm_num,le_antisymm (h▸Cardinal.mk_subtype_mono fun and=>And.left) (not_lt.1 fun and=>? _), fun and⟨⟨A, B, _⟩, _⟩x⟨⟨D,E, _⟩, _⟩=>?_
          · rw[←Set.diff_union_inter (_ ''_) R,Cardinal.mk_union_of_disjoint] at h
            · use(Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum and ((Cardinal.le_one_iff_subsingleton.2 ⟨fun⟨ _,⟨A, B, rfl⟩,M⟩⟨ _,⟨D,E, rfl⟩,F⟩=>Subtype.eq ?_⟩).trans_lt ?_)).ne h
              · apply Cardinal.nat_lt_continuum
              exact ( (L _) M _ F D E.1 A B.1 (by ring)).resolve_right (by bound) |>.1
            use Set.disjoint_sdiff_inter
          use‹_=and›▸‹_ = _›▸mt (L A B.1 a (by valid) D E.1 _ · (by ring)) (·.elim (B.2 ·.1) (E.2 ·.2))
        cases h (by rwa[Cardinal.mk_image_eq_of_injOn _ _ sub_left_injective.injOn])
      rcases h ↑(le_antisymm (@Cardinal.mk_real▸Cardinal.mk_set_le _) (by assumption) )
    cases(( R.diff_union_of_subset (R.singleton_subset_iff.2 (by valid))▸Cardinal.mk_union_le _ _).trans_lt ↑(Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum (not_le.1 h) (Cardinal.mk_lt_aleph0.trans (Cardinal.cantor _) ) )).ne (by valid)
  let:=Cardinal.mk_real.symm
  replace:Cardinal.mk {s |s ∉R∧s+s ∉R}=.continuum
  · erw [←Set.ext fun and=>not_or,Cardinal.mk_compl_of_infinite, this]
    match(this▸Cardinal.mk_set_le R).lt_of_ne a with | S=>exact (Cardinal.mk_union_le _ _).trans_lt (this▸Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum S (S.trans_le' ⟨(⟨ _,·.2⟩), fun and=>by grind⟩))
  let⟨x,k,l⟩ :=zorn_subset { s ⊆{S ∉R | S+S ∉R}|∀S ∈ s,∀T ∈ s,S+T ∉R} fun and p=>?_
  · use x,fun R M=>(k.1 M).1,le_antisymm (this▸Cardinal.mk_subtype_mono k.1) (not_lt.mp fun and=>a.comp (le_antisymm (Cardinal.mk_real▸Cardinal.mk_set_le R)) ? _), (by use k.2 · · · ·)
    replace l:{s |s ∉R∧s+s ∉R} ⊆x∪⋃ a ∈x,R.image (·-a)
    · use fun and i=>or_iff_not_imp_right.2 (l ⟨x.insert_subset i k.1,by_contra fun and=>. (by_contra (and ∘by field_simp+contextual[i.symm, sub_eq_iff_eq_add,add_comm,k.2]))⟩ (by norm_num) (.inl rfl))
    convert not_lt.mp fun and' =>(this▸(Cardinal.mk_subtype_mono l).trans.comp (Cardinal.mk_union_le _ _).trans (add_le_add_left (Cardinal.mk_biUnion_le _ _) @_)).not_lt @_
    exact (Cardinal.add_lt_of_lt ↑Cardinal.aleph0_le_continuum and) (Cardinal.mul_lt_of_lt ↑Cardinal.aleph0_le_continuum and ((ciSup_le' fun and=>Cardinal.mk_image_le).trans_lt and'))
  exact ( ⟨_, ⟨sSup_le (p.trans (inf_le_left)),fun μ ⟨a, A, R⟩ L ⟨a, B, M⟩=>·.total A B|>.elim ( fun and=>(p B).2 μ (and R) L M) fun and=>(p A).2 μ R L (and M)⟩, fun and=>le_sSup⟩)

end Erdos949
