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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 741

*References:*
 - [erdosproblems.com/741](https://www.erdosproblems.com/741)
 - [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
    Math. Pannon. (1994), 261-269.
-/

open scoped Pointwise
open Set

namespace Erdos741




/-- Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive density?

Note that this is using a literal interpretation of "positive density".

This was disproved by the DeepMind prover agent.
-/
--@[category research solved, AMS 5,
--formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/486bc8afae062b6711cd16d3466d651ee2880a52/FormalConjectures/ErdosProblems/741.lean#L1449"]
theorem erdos_741.parts.i : answer(False) ↔ ∀ A : Set ℕ, HasPosDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ HasPosDensity (A₁ + A₁)
    ∧ HasPosDensity (A₂ + A₂) := by
  sorry

/--
Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive lower density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive lower density?
-/
@[category research open, AMS 5]
theorem erdos_741.variants.lower : answer(sorry) ↔ ∀ A : Set ℕ, 0 < lowerDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < lowerDensity (A₁ + A₁)
    ∧ 0 < lowerDensity (A₂ + A₂) := by
  sorry

lemma upperDensity_pos_implies_seq (S : Set ℕ) (h : 0 < upperDensity S) :
    ∃ c > 0, ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ k, c ≤ (Set.ncard (S ∩ Set.Iic (f k)) : ℝ) / (f k : ℝ) := by
  delta upperDensity at h
  simp_all[Set.partialDensity,Filter.limsup_eq]
  refine(exists_between h).imp fun and(a)=> ⟨a.1,((Classical.axiomOfChoice fun and=>not_forall.1 (not_le.2 a.2<|csInf_le (not_imp_comm.1 Real.sInf_of_not_bddBelow h.ne') ⟨and+1,·⟩)).elim) ?_⟩
  use fun and f=>⟨ (and ∘.rec 0 _),strictMono_nat_of_lt_succ fun and=>not_forall.1 (f _)|>.1, fun and=> (not_le.1 (f _ fun and=>.)).le.trans (div_le_div_of_nonneg_right (mod_cast ? _) (by bound))⟩
  exact (Set.ncard_le_ncard fun and=>.imp_right (@·.out.le))


lemma exists_N_sparse (A : Set ℕ) (c : ℝ) (hc : 0 < c)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (h_sum : ∀ k, c ≤ (Set.ncard ((A + A) ∩ Set.Iic (f k)) : ℝ) / (f k : ℝ))
    (h_sparse : upperDensity A ≤ 0) (K : ℕ) :
    ∃ N : ℕ, N > K ∧ (K + 1 : ℝ) * (Set.ncard (A ∩ Set.Iic N) : ℝ) ≤ (c / 4) * (N : ℝ) ∧
             c ≤ (Set.ncard ((A + A) ∩ Set.Iic N) : ℝ) / (N : ℝ) := by
  simp_rw [upperDensity,.>.]at *
  simp_all[Filter.limsup_eq, A.inter_comm, true,Set.partialDensity]
  obtain ⟨y,@c, _⟩:=exists_lt_of_csInf_lt (by use 1,1, fun and x =>div_le_one_of_le₀ (mod_cast(Nat.card_mono (.of_fintype _) fun and=>And.left).trans (by bound)) and.cast_nonneg) (h_sparse.trans_lt (by bound:c/4/ (K+1)>0))
  apply(((tendsto_natCast_atTop_atTop.comp hf.tendsto_atTop).const_mul_atTop ↑(sub_pos.2 (by assumption):)).eventually_ge_atTop ((K+1)*y)).and (Filter.mem_atTop (K+1+c))|>.exists.elim
  use fun and h=>⟨ _,le_self_add.trans (h.2.trans hf.le_apply), (le_inv_mul_iff₀ (by positivity)).1 ? _,h_sum and⟩
  use .trans (mod_cast Nat.card_mono (.of_fintype _) fun and=>.imp_left and.lt_succ.2) ( ((div_le_iff₀ (by bound)).1 ((‹∀ (x _),_› (f and+1) (by linarith[hf.le_apply.trans' h.2]):))).trans (?_))
  exact (.trans (by rw [Nat.cast_succ]) ((ge_of_eq (by rw [inv_mul_eq_div, mul_div_right_comm])).trans' (by nlinarith![(‹∀ (x _),_≤y› and (by valid)).trans' (by positivity)])))


lemma exists_rapid_seq (P : ℕ → ℕ → Prop) (h_inf : ∀ K, ∃ N > K, P K N) :
    ∃ M : ℕ → ℕ, StrictMono M ∧ ∀ k, P (M k) (M (k + 1)) := by
  exact (Classical.axiomOfChoice ↑h_inf).elim fun and(a)=>⟨.rec 0 _,strictMono_nat_of_lt_succ fun and=>(a _).left, fun and=>(a _).right⟩

theorem Erdos741.upperDensity_pos_implies_seq.extracted_1_3 (S : Set ℕ)
  (h : 0 < sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → (b : ℝ)⁻¹ * ↑(Fintype.card ↑(Iio b ∩ S)) ≤ a}) (and_1 : ℝ)
  (x : 0 < and_1 ∧ and_1 < sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → (b : ℝ)⁻¹ * ↑(Fintype.card ↑(Iio b ∩ S)) ≤ a})
  (A : 0 < and_1) (B : and_1 < sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → (b : ℝ)⁻¹ * ↑(Fintype.card ↑(Iio b ∩ S)) ≤ a})
  (and_2 : ℕ → ℕ) (m : ∀ (x : ℕ), ¬(x + 1 ≤ and_2 x → (↑(and_2 x))⁻¹ * ↑(Fintype.card ↑(Iio (and_2 x) ∩ S)) ≤ and_1))
  (and : ℕ) :
  ↑(Fintype.card ↑(Iio (and_2 ((fun t ↦ Nat.rec 0 (fun and ↦ and_2) t) and)) ∩ S)) ≤
    ↑(Fintype.card ↑(Iic ((and_2 ∘ fun t ↦ Nat.rec 0 (fun and ↦ and_2) t) and) ∩ S)) := by
    use Set.card_le_card fun and=>.imp_left (·.out.le)

lemma upperDensity_add_self_pos (A : Set ℕ) (h : 0 < upperDensity A) :
    0 < upperDensity (A + A) := by
  delta upperDensity at*
  norm_num [Set.partialDensity] at h⊢
  simp_rw [Filter.limsup_eq] at h⊢
  use (half_pos h).trans_le (le_csInf ⟨1,.of_forall fun and=>div_le_one_of_le₀ (mod_cast(Nat.card_mono (.of_fintype _) fun and=>And.right).trans (by(norm_num))) and.cast_nonneg⟩ fun and(p) =>p.exists_forall_of_atTop.elim fun and=>? _)
  use(div_le_iff₀ (by norm_num)).2.comp (csInf_le (not_imp_comm.1 Real.sInf_of_not_bddBelow h.ne')) ∘Filter.eventually_atTop.2 ∘.intro and ∘ fun and R L=>.trans (?_) (mul_le_mul_of_nonneg_right le_rfl ? _)
  · use(A ∩.Iio R).eq_empty_or_nonempty.elim (by norm_num[ (and R L).trans',div_nonneg _,.]) fun ⟨a, E⟩=>.trans (?_) (mul_le_mul_of_nonneg_right (and (2 *R) (by valid)) (2).cast_nonneg)
    norm_num[Nat.add_lt_add, two_mul,div_mul,div_le_div_of_nonneg_right _,Set.ncard_le_ncard_of_injOn _ ↑_ (add_left_injective a).injOn (.of_fintype _),A.add_mem_add, E.1, E.2.out]
    exact (div_le_div_of_nonneg_right) (mod_cast Set.ncard_le_ncard_of_injOn _ ( fun and=>.imp (by exists _,·, a, E.1) (and.add_lt_add · E.2)) fun and=>by valid) R.cast_nonneg
  · norm_num

lemma exists_N_dense (A : Set ℕ) (c : ℝ) (hc : 0 < c)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (h_dense : ∀ k, c ≤ (Set.ncard (A ∩ Set.Iic (f k)) : ℝ) / (f k : ℝ))
    (K : ℕ) :
    ∃ N : ℕ, N > K ∧ (Set.ncard (A ∩ Set.Iic K) : ℝ) ≤ (c / 4) * (N : ℝ) ∧
             c ≤ (Set.ncard (A ∩ Set.Iic N) : ℝ) / (N : ℝ) := by
  exact ⟨ _,le_sup_left.trans hf.le_apply,(div_le_iff₀' (by positivity)).1 ↑(Nat.ceil_le.mp.comp (le_sup_right).trans (hf).le_apply), (h_dense _)⟩

def in_block (M : ℕ → ℕ) (x : ℕ) : Prop :=
  ∃ k, M (2 * k) < x ∧ x ≤ M (2 * k + 1)

def block_set (M : ℕ → ℕ) : Set ℕ := {x | in_block M x}

lemma case_dense_bounds (A : Set ℕ) (c : ℝ) (hc : 0 < c) (M : ℕ → ℕ) (hM_mono : StrictMono M)
    (hM : ∀ k, (Set.ncard (A ∩ Set.Iic (M k)) : ℝ) ≤ (c / 4) * (M (k + 1) : ℝ) ∧
               c ≤ (Set.ncard (A ∩ Set.Iic (M (k + 1))) : ℝ) / (M (k + 1) : ℝ)) :
    0 < upperDensity (A ∩ block_set M) ∧ 0 < upperDensity (A \ block_set M) := by
  delta upperDensity block_set
  simp_all[ Erdos741.in_block,Filter.limsup_eq,le_div_iff₀,(hM_mono (by constructor)).pos,Set.partialDensity]
  use ((div_pos hc four_pos).trans_le) (le_csInf ⟨1,1,fun R L=>div_le_one_of_le₀ (mod_cast(Nat.card_mono (.of_fintype _) fun and=>And.right).trans (by norm_num)) R.cast_nonneg⟩ fun and ⟨a, _⟩=>? _)
  · use(div_pos hc four_pos).trans_le (le_csInf ⟨1,1, fun and x =>(div_le_one (by bound)).2 (mod_cast(Nat.card_mono (.of_fintype _) inf_le_right).trans ( (by bound)))⟩ fun and ⟨a, _⟩=>? _)
    apply((le_div_iff₀ (by bound)).mpr _).trans ( (by assumption :) ( M (2 *(a) +2)+1) ↑(.trans (by valid) (hM_mono.le_apply.trans_lt ↑(Nat.lt_succ_self ↑_))))
    use(@Nat.cast_succ ℝ _ _▸not_lt.1 fun and=>(((hM (2 *a + 1)).2.trans (mod_cast(?_))).trans_lt (add_lt_add_of_le_of_lt (hM (2 *a + 1)).1 and)).asymm ? _)
    · linear_combination c/2*(mod_cast(hM_mono (by constructor)).pos: (1:ℝ) ≤M _) +hc/4
    use(Set.ncard_le_ncard (↑ fun and⟨A, B⟩=>or_not.imp ?_ (by use⟨A,.⟩,and.lt_succ_of_le B))).trans ↑(Set.ncard_union_le _ _)
    exact (fun ⟨a, R, C⟩=>by use A,C.trans (hM_mono.monotone ((by valid ∘hM_mono.lt_iff_lt.1) (R.trans_le B))))
  · apply((le_div_iff₀ (by bound)).2 _).trans ( (by valid :) ( _) (a.le_succ_of_le ↑(.trans (by valid) (hM_mono).le_apply : M (2 *(a)+1)≥ _) ) )
    replace: A ∩.Iic (M (2 *a + 1)) ⊆A ∩.Iic (M (2 * a))∪(A ∩{s |∃a,M (2 *a)<s ∧s≤M (2 *a+1)}) ∩ Iio (M (2 *a+1)+1)
    · exact fun and⟨A, B⟩=>(lt_or_ge _ _).elim (.inr ⟨⟨A,a,., B⟩,and.lt_succ.2 B⟩) (.inl ∘.intro A)
    use .trans (by rw [Nat.cast_succ]) (not_lt.1 fun and=>? _)
    have := (Set.ncard_le_ncard this).trans (Set.ncard_union_le _ _)
    linarith[(hM _).2.trans (.trans (Nat.cast_le.2 this) (Nat.cast_add _ _).le),hM (2 *a), mul_le_mul_of_nonneg_left (mod_cast(hM_mono (by constructor)).pos: (1:ℝ) ≤M (2 *a + 1)) hc.le]

lemma sumset_diff_bound (A A₁ A₂ : Set ℕ) (N K : ℕ)
    (h_union : A = A₁ ∪ A₂) (hK : ∀ x ∈ A₂ ∩ Set.Iic N, x ≤ K) :
    Set.ncard ((A + A) ∩ Set.Iic N) ≤ Set.ncard ((A₁ + A₁) ∩ Set.Iic N) + (K + 1) * Set.ncard (A ∩ Set.Iic N) := by
  have h_sum_union : (A + A) ∩ Set.Iic N ⊆ ((A₁ + A₁) ∩ Set.Iic N) ∪ ((A₂ + A) ∩ Set.Iic N) := by norm_num[*,Set.union_inter_distrib_right]
                                                                                                  use fun and⟨ ⟨a, L, T, M, E⟩, _⟩=> L.rec ( fun and=>? _) fun and=>.inr (by use (by use a, and, T))
                                                                                                  use M.imp (by use ⟨a, and, T,., E⟩) (by use⟨ _, ·, a, L, E▸add_comm _ _⟩)
  have h_card1 : Set.ncard ((A + A) ∩ Set.Iic N) ≤ Set.ncard ((A₁ + A₁) ∩ Set.Iic N) + Set.ncard ((A₂ + A) ∩ Set.Iic N) := by exact (Set.ncard_le_ncard (by valid)).trans (Set.ncard_union_le _ _)
  have h_A2A : (A₂ + A) ∩ Set.Iic N ⊆ (A₂ ∩ Set.Iic K) + (A ∩ Set.Iic N) := by refine fun and⟨ ⟨a, A, P, B, E⟩, R⟩=>by cases E with use a, ⟨A,hK a ⟨A,le_self_add.trans R.out⟩⟩, P, ⟨B,le_add_self.trans R.out⟩
  have h_card_A2A : Set.ncard ((A₂ + A) ∩ Set.Iic N) ≤ (K + 1) * Set.ncard (A ∩ Set.Iic N) := by exact (Set.ncard_le_ncard h_A2A).trans (Set.natCard_add_le.trans (Nat.mul_le_mul_right _ (K.card_Iic▸Nat.card_eq_finsetCard _▸Nat.card_mono (.of_fintype _) (by bound))))
  linarith

lemma case_sparse_bounds (A : Set ℕ) (c : ℝ) (hc : 0 < c) (M : ℕ → ℕ) (hM_mono : StrictMono M)
    (hM : ∀ k, (M k + 1 : ℝ) * (Set.ncard (A ∩ Set.Iic (M (k + 1))) : ℝ) ≤ (c / 4) * (M (k + 1) : ℝ) ∧
               c ≤ (Set.ncard ((A + A) ∩ Set.Iic (M (k + 1))) : ℝ) / (M (k + 1) : ℝ)) :
    0 < upperDensity ((A ∩ block_set M) + (A ∩ block_set M)) ∧
    0 < upperDensity ((A \ block_set M) + (A \ block_set M)) := by
  have h_union1 : A = (A ∩ block_set M) ∪ (A \ block_set M) := by norm_num
  have h_union2 : A = (A \ block_set M) ∪ (A ∩ block_set M) := by norm_num
  have h_bound1 : ∀ k, Set.ncard ((A + A) ∩ Set.Iic (M (2 * k + 1))) ≤ Set.ncard (((A ∩ block_set M) + (A ∩ block_set M)) ∩ Set.Iic (M (2 * k + 1))) + (M (2 * k) + 1) * Set.ncard (A ∩ Set.Iic (M (2 * k + 1))) := by
    intro k
    have hk_max : ∀ x ∈ (A \ block_set M) ∩ Set.Iic (M (2 * k + 1)), x ≤ M (2 * k) := by use fun and(a)=>not_lt.1 (a.1.2 ⟨ _,., a.2⟩)
    exact sumset_diff_bound A (A ∩ block_set M) (A \ block_set M) (M (2 * k + 1)) (M (2 * k)) h_union1 hk_max
  have h_bound2 : ∀ k, Set.ncard ((A + A) ∩ Set.Iic (M (2 * k + 2))) ≤ Set.ncard (((A \ block_set M) + (A \ block_set M)) ∩ Set.Iic (M (2 * k + 2))) + (M (2 * k + 1) + 1) * Set.ncard (A ∩ Set.Iic (M (2 * k + 2))) := by
    intro k
    have hk_max : ∀ x ∈ (A ∩ block_set M) ∩ Set.Iic (M (2 * k + 2)), x ≤ M (2 * k + 1) := by norm_num[block_set]
                                                                                             norm_num[in_block]
                                                                                             refine fun and R L a s α=>s.trans ( (hM_mono).monotone (not_lt.mp (a.not_ge ∘α.trans ∘ (hM_mono.monotone <|Nat.mul_le_mul_left (2)<|Nat.lt_of_mul_lt_mul_left ·.le_pred))))
    exact sumset_diff_bound A (A \ block_set M) (A ∩ block_set M) (M (2 * k + 2)) (M (2 * k + 1)) h_union2 hk_max
  have h_dens1 : ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ k, 3 * c / 4 ≤ (Set.ncard (((A ∩ block_set M) + (A ∩ block_set M)) ∩ Set.Iic (f k)) : ℝ) / (f k : ℝ) := by refine ⟨ _,hM_mono.comp (strictMono_id.const_mul two_pos |>.add_const (1)), fun and=>(le_div_iff₀ (mod_cast(hM_mono (by constructor)).pos)).mpr ?_⟩
                                                                                                                                                          linarith![((le_div_iff₀ (mod_cast(hM_mono (by constructor)).pos)).1 (hM (2 *and)).right).trans (.trans (Nat.cast_le.2 (h_bound1 and)) (by rw [Nat.cast_add,Nat.cast_mul,Nat.cast_succ])),hM (2 *and)]
  have h_dens2 : ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ k, 3 * c / 4 ≤ (Set.ncard (((A \ block_set M) + (A \ block_set M)) ∩ Set.Iic (f k)) : ℝ) / (f k : ℝ) := by refine ⟨ _,hM_mono.comp ((strictMono_id.const_mul two_pos).add_const 2), fun and=>(le_div_iff₀ (mod_cast(hM_mono (by constructor)).pos)).2 ?_⟩
                                                                                                                                                          linarith![hM (2 *and+1), (le_div_iff₀ (mod_cast(hM_mono (by constructor)).pos)).1 (hM (2 *and + 1)).2|>.trans ((Nat.cast_le.2 (h_bound2 _)).trans ((by rw [Nat.cast_add,Nat.cast_mul,Nat.cast_succ])))]
  have h_pos1 : 0 < upperDensity ((A ∩ block_set M) + (A ∩ block_set M)) := by delta Set.upperDensity
                                                                               norm_num[Filter.limsup_eq,Set.partialDensity]
                                                                               use(div_pos hc four_pos).trans_le (le_csInf ⟨1,1,fun R L=>div_le_one_of_le₀ (mod_cast(Nat.card_mono (.of_fintype _) inf_le_right).trans ( (by norm_num))) R.cast_nonneg⟩ fun and ⟨a, _⟩=>? _)
                                                                               use((le_div_iff₀ (by bound)).2 ? _).trans ( (by valid:) (M (2 *a+1)+1) (by linarith[hM_mono.le_apply.trans' (2 *a+1).le_refl]))
                                                                               use@Nat.cast_succ ℝ _ _▸.trans (?_) (Nat.cast_le.2 (Nat.card_mono (.of_fintype _) fun and=>.imp_right and.lt_succ_of_le))
                                                                               have := (le_div_iff₀ ↑(mod_cast(hM_mono (by constructor)).pos)).mp (hM (2 * a)).2 |>.trans ( Nat.cast_le.mpr (h_bound1 a))
                                                                               linarith![hM (2 *a), mul_le_mul_of_nonneg_left (mod_cast(hM_mono (by constructor)).pos: (1:ℝ) ≤M (2 *a + 1)) hc.le, this.trans (by rw [Nat.cast_add,Nat.cast_mul,Nat.cast_succ])]
  have h_pos2 : 0 < upperDensity ((A \ block_set M) + (A \ block_set M)) := by delta Set.upperDensity
                                                                               norm_num[Filter.limsup_eq,Set.partialDensity]
                                                                               use(div_pos (mul_pos three_pos hc) four_pos).trans_le (h_dens2.elim fun and x =>le_csInf ⟨1,1,fun A B=>div_le_one_of_le₀ (mod_cast ? _) A.cast_nonneg⟩ fun and ⟨a, H⟩=>? _)
                                                                               · exact (Nat.card_mono (.of_fintype _) fun and=>And.right).trans (by {norm_num})
                                                                               use not_lt.1 fun and=>(((tendsto_natCast_atTop_atTop.comp x.1.tendsto_atTop).atTop_mul_const ↑(sub_pos.2 and)).eventually_gt_atTop (3*c/4)).frequently<|Filter.eventually_atTop.2 ⟨a+1,?_⟩
                                                                               use fun and α=> fun and' =>absurd.comp (div_le_iff₀ (by bound)).1 (H _ (le_of_lt (α.trans (x.1.le_apply.trans (Nat.le_succ _))))) (@Nat.cast_succ ℝ _ _▸? _)
                                                                               exact (mt ((le_div_iff₀ (mod_cast(x.1 α).pos)).1 (x.2 _)).trans (by linarith!) ∘.trans (congr_arg _ ((congr_arg _) ((Set.ext fun and=>and_congr_right' and.lt_succ)))).ge)
  exact ⟨h_pos1, h_pos2⟩

lemma exists_partition_positive_density (A : Set ℕ) (hA : 0 < upperDensity A) :
    ∃ A₁ A₂, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity A₁ ∧ 0 < upperDensity A₂ := by
  have ⟨c, hc, f, hf, h_bound⟩ := upperDensity_pos_implies_seq A hA
  have h_inf : ∀ K, ∃ N : ℕ, N > K ∧ (Set.ncard (A ∩ Set.Iic K) : ℝ) ≤ (c / 4) * (N : ℝ) ∧ c ≤ (Set.ncard (A ∩ Set.Iic N) : ℝ) / (N : ℝ) :=
    exists_N_dense A c hc f hf h_bound
  have ⟨M, hM_mono, hM⟩ := exists_rapid_seq (fun K N => (Set.ncard (A ∩ Set.Iic K) : ℝ) ≤ (c / 4) * (N : ℝ) ∧ c ≤ (Set.ncard (A ∩ Set.Iic N) : ℝ) / (N : ℝ)) (by intro K; have ⟨N, hN_gt, hN⟩ := h_inf K; exact ⟨N, hN_gt, hN⟩)
  have ⟨h_pos1, h_pos2⟩ := case_dense_bounds A c hc M hM_mono hM
  have h_union : A = (A ∩ block_set M) ∪ (A \ block_set M) := by norm_num
  have h_disj : Disjoint (A ∩ block_set M) (A \ block_set M) := by exact ↑disjoint_inf_sdiff
  exact ⟨A ∩ block_set M, A \ block_set M, h_union, h_disj, h_pos1, h_pos2⟩

lemma case_dense_A (A : Set ℕ) (hA : 0 < upperDensity A) :
    ∃ A₁ A₂, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity (A₁ + A₁) ∧ 0 < upperDensity (A₂ + A₂) := by
  have ⟨A₁, A₂, h_union, h_disj, h_pos1, h_pos2⟩ := exists_partition_positive_density A hA
  exact ⟨A₁, A₂, h_union, h_disj, upperDensity_add_self_pos A₁ h_pos1, upperDensity_add_self_pos A₂ h_pos2⟩

lemma case_sparse_A (A : Set ℕ) (hA_sum : 0 < upperDensity (A + A)) (hA_sparse : upperDensity A ≤ 0) :
    ∃ A₁ A₂, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity (A₁ + A₁) ∧ 0 < upperDensity (A₂ + A₂) := by
  have ⟨c, hc, f, hf, h_bound⟩ := upperDensity_pos_implies_seq (A + A) hA_sum
  have h_inf : ∀ K, ∃ N : ℕ, N > K ∧ (K + 1 : ℝ) * (Set.ncard (A ∩ Set.Iic N) : ℝ) ≤ (c / 4) * (N : ℝ) ∧ c ≤ (Set.ncard ((A + A) ∩ Set.Iic N) : ℝ) / (N : ℝ) :=
    exists_N_sparse A c hc f hf h_bound hA_sparse
  have ⟨M, hM_mono, hM⟩ := exists_rapid_seq (fun K N => (K + 1 : ℝ) * (Set.ncard (A ∩ Set.Iic N) : ℝ) ≤ (c / 4) * (N : ℝ) ∧ c ≤ (Set.ncard ((A + A) ∩ Set.Iic N) : ℝ) / (N : ℝ)) (by intro K; have ⟨N, hN_gt, hN⟩ := h_inf K; exact ⟨N, hN_gt, hN⟩)
  have ⟨h_pos1, h_pos2⟩ := case_sparse_bounds A c hc M hM_mono hM
  have h_union : A = (A ∩ block_set M) ∪ (A \ block_set M) := by norm_num[]
  have h_disj : Disjoint (A ∩ block_set M) (A \ block_set M) := by use disjoint_inf_sdiff
  exact ⟨A ∩ block_set M, A \ block_set M, h_union, h_disj, h_pos1, h_pos2⟩

/--
Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive upper density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive upper density?

The DeepMind prover agent found a formal proof for this statement
-/
@[category research solved, AMS 5]
theorem erdos_741.variants.upper : answer(True) ↔ ∀ A : Set ℕ, 0 < upperDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity (A₁ + A₁)
    ∧ 0 < upperDensity (A₂ + A₂) := by
  constructor
  · intro _ A hA_sum
    by_cases hA : 0 < upperDensity A
    · exact case_dense_A A hA
    · have hA_sparse : upperDensity A ≤ 0 := not_lt.mp hA
      exact case_sparse_A A hA_sum hA_sparse
  · intro _
    trivial

/--
Is there a basis $A$ of order $2$ such that if $A=A_1\sqcup A_2$ then $A_1+A_1$ and $A_2+A_2$
cannot both have bounded gaps?

This was proved by DeepMind prover agent.
 -/
@[category research solved, AMS 5,
formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/486bc8afae062b6711cd16d3466d651ee2880a52/FormalConjectures/ErdosProblems/741.lean#L1629"]
theorem erdos_741.parts.ii : answer(True) ↔ ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂,
    A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬ (IsSyndetic (A₁ + A₁) ∧ IsSyndetic (A₂ + A₂)) := by
  sorry


end Erdos741
