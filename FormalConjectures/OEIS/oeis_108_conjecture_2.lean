/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Nat Real Finset

/--
A000108 Catalan numbers: C(n) = binomial(2n,n)/(n+1).
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalan_reciprocal_sum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum a_rat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def oeis_108_index_cond (j k : ℕ) : Prop :=
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k

open Int (fract)

/-- The fractional part of a rational number, viewed as a real number. Must be noncomputable
due to dependence on the real floor function. -/
noncomputable def frac_part (q : ℚ) : ℝ := fract (q : ℝ)

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START

lemma choose_ge (n : ℕ) : n + 1 ≤ Nat.choose (2 * n) n := by
  exact n.casesOn (by constructor) fun and=>.trans (by simp_all) ( (and+2).choose_le_choose (↑ _) (by valid ) )

lemma a_pos (n : ℕ) : 0 < a n := by
  show (0<star _)
  exact ( (n + 1)).div_pos (n.eq_zero_or_pos.elim (by bound) (.trans (by simp_all) ∘ (n + 1).choose_le_choose n ∘by valid)) n.succ_pos

lemma a_recurrence (n : ℕ) : (n + 2) * a (n + 1) = 2 * (2 * n + 1) * a n := by
  simp_rw [ two_mul, a]
  rw [Nat.mul_div_cancel' (n.succ.succ_dvd_centralBinom.trans (by rw [Nat.centralBinom])), mul_add, ←Nat.mul_div_assoc _ (n.succ_dvd_centralBinom.trans (by rw [Nat.centralBinom]))]
  exact (Nat.eq_div_of_mul_eq_left (nofun) (by nlinarith[ (2 *n+1).succ_mul_choose_eq (n : ℕ), (2 *n).succ_mul_choose_eq (n : ℕ), (2 *n+1).choose_succ_succ n]))

lemma a_grow (n : ℕ) (hn : 2 ≤ n) : 5 * a n ≤ 2 * a (n + 1) := by
  simp_rw [a,mul_comm]
  rw [←Nat.mul_div_assoc (2) (by_contra fun and=>absurd (( (n + 1)*2).choose_succ_right_eq (n + 1)) fun and=>absurd ((n*2).choose_succ_right_eq n) ? _),n.succ_mul,Nat.le_div_iff_mul_le (by valid)]
  · nlinarith[((n*2).choose n).mul_div_le (n + 1),(n*2+1).succ_mul_choose_eq (n : ℕ),(n*2).succ_mul_choose_eq (n : ℕ),(n*2+1).choose_succ_succ n]
  · rcases‹¬_›.comp (Nat.Coprime.dvd_mul_right (by·norm_num [Nat.add_sub_cancel _,mul_two])).1 (and▸dvd_mul_left _ _)

lemma a_rat_pos (n : ℕ) : 0 < a_rat n := by
  rw [←not_le, a_rat]
  simp_all[a]
  cases n with·norm_num[ ((Nat.choose_le_choose _) ↑(lt_mul_left ↑(Nat.succ_pos _) ↑ _)).trans_lt']

lemma a_rat_grow (n : ℕ) (hn : 2 ≤ n) : a_rat (n + 1) ≤ (2 / 5 : ℚ) * a_rat n := by
  norm_num only[a_rat,div_mul_eq_mul_div]
  delta a
  repeat rw [Nat.cast_div (by_contra fun and=>absurd ((2* (n + 1)).choose_succ_right_eq (n + 1)) fun and=>absurd ((2*n).choose_succ_right_eq n) ? _) (by cases ·)]
  · push_cast [Nat.cast_choose, two_mul,le_add_self,Nat.add_sub_cancel, mul_div,inv_div,div_div]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (n.succ_add (n + 1)▸(n+n+1).factorial_succ▸(n+n).factorial_succ▸mod_cast n.factorial_succ▸by match n with | S+2=>grind)
  · exact (by assumption ∘(Nat.Coprime.dvd_mul_right (by·norm_num[two_mul, n.add_sub_cancel])).1 ∘dvd_of_mul_left_eq _)
  · cases‹¬_›.comp (Nat.Coprime.dvd_mul_right (by norm_num[two_mul,Nat.add_sub_cancel _ _])).1 (and▸dvd_mul_left _ _)

lemma a_rat_sum_bound (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
  ∑ i ∈ Finset.Icc (j + 1) k, a_rat i ≤ (2 / 3 : ℚ) * a_rat j - (2 / 3 : ℚ) * a_rat k := by
  simp_rw [div_mul_eq_mul_div, a_rat]
  delta and a
  repeat rewrite [ Nat.cast_div (by_contradiction fun and=> absurd ((2*j).choose_succ_right_eq j) fun and' => absurd ((2*k).choose_succ_right_eq k) ? _) (by norm_cast)]
  · refine j.le_induction (by norm_num) ( fun and A B=>(((( Finset.sum_Icc_succ_top (by valid) _)).trans_le (add_le_add B ? _)).trans_eq (sub_add_sub_cancel _ _ _))) k hjk
    field_simp[Nat.cast_choose, two_mul,Nat.succ_dvd_centralBinom (@ _)|>.trans, true,Nat.centralBinom]
    rw[Nat.cast_div (by_contra fun and' =>absurd ((2* (and+1)).choose_succ_right_eq (and+1)) ? _) (by cases.),div_div_eq_mul_div,div_sub_div _ _ (mod_cast Nat.choose_ne_zero (by valid)) (mod_cast Nat.choose_ne_zero (by valid))]
    · use(mul_div_mul_left _ _<|mod_cast Nat.choose_ne_zero (by valid)).ge.trans.comp (div_le_div_of_nonneg_right ((le_sub_iff_add_le.2 (mod_cast(2).mul_succ and▸?_)).trans (mul_sub _ _ _).ge) (by·hint)).trans (mul_assoc _ _ _).le
      nlinarith only[hj.trans A, (2 *and+1).succ_mul_choose_eq and, (2 *and).succ_mul_choose_eq and, (2 *and+1).choose_succ_succ and]
    · use (and'.comp (Nat.Coprime.dvd_mul_right (by norm_num[two_mul,Nat.add_sub_cancel _ _])).1 ∘dvd_of_mul_left_eq _)
  · exact (and.comp (Nat.Coprime.dvd_mul_right (by norm_num[two_mul,k.add_sub_cancel])).1 ∘dvd_of_mul_left_eq _)
  · rcases and.comp (Nat.Coprime.dvd_mul_right (by·norm_num [j.add_sub_cancel, two_mul])).1 (and'▸dvd_mul_left _ _)

lemma a_two : a 2 = 2 := by rfl

lemma a_rat_two : a_rat 2 = 1 / 2 := by
  norm_num [a_rat]
  apply (one_div (2)).symm

lemma a_ge_two (j : ℕ) (hj : 2 ≤ j) : 2 ≤ a j := by
  delta a
  exact (Nat.le_div_iff_mul_le j.succ_pos).mpr ((2).le_induction (by decide) (fun F R L=> (2 *F+1).choose_succ_succ F▸ (2 *F).choose_succ_succ F▸by linarith [ (2 *F).choose_le_succ F]) j @hj)

lemma a_rat_le_half (j : ℕ) (hj : 2 ≤ j) : a_rat j ≤ 1 / 2 := by
  norm_num only[ a_rat]
  delta a
  use (inv_anti₀ rfl (Nat.cast_le.2 ((Nat.le_div_iff_mul_le j.succ_pos).2 ((2).le_induction (by decide) (fun F a s=> (2 *F+1).choose_succ_succ F▸ (2 *F).choose_succ_succ F▸? _) j hj)))).trans (one_div 2).ge
  bound[ (2 *F).choose_le_succ F]

lemma catalan_reciprocal_sum_pos (j k : ℕ) (h : j ≤ k) :
  0 < catalan_reciprocal_sum j k := by
  simp_rw [catalan_reciprocal_sum,.≤·] at h⊢
  refine Finset.sum_pos (fun R M=>lt_of_lt_of_le ?_ (by rw [a_rat])) (by bound)
  simp_all[a]
  use R.casesOn one_pos fun and=>(Nat.choose_le_choose _ (lt_mul_left and.succ_pos (by decide))).trans' (by norm_num)

lemma catalan_reciprocal_sum_rw (j k : ℕ) (h : j ≤ k) :
  catalan_reciprocal_sum j k = a_rat j + ∑ i ∈ Finset.Icc (j + 1) k, a_rat i := by
  delta catalan_reciprocal_sum
  apply Finset.sum_eq_sum_Ico_succ_bot (by(omega ) )

lemma catalan_reciprocal_sum_lt_one (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
  catalan_reciprocal_sum j k < 1 := by
  rw [catalan_reciprocal_sum_rw j k hjk]
  have h1 := a_rat_sum_bound j k hj hjk
  have h2 : a_rat j + ∑ i ∈ Finset.Icc (j + 1) k, a_rat i ≤ a_rat j + (2 / 3 : ℚ) * a_rat j - (2 / 3 : ℚ) * a_rat k := by linarith
  have hp : 0 < (2 / 3 : ℚ) * a_rat k := by
    have hpos : 0 < a_rat k := a_rat_pos k
    linarith
  have h3 : a_rat j + (2 / 3 : ℚ) * a_rat j - (2 / 3 : ℚ) * a_rat k < a_rat j + (2 / 3 : ℚ) * a_rat j := sub_lt_self _ hp
  have h4 : a_rat j + (2 / 3 : ℚ) * a_rat j = (5 / 3 : ℚ) * a_rat j := by ring
  have h5 : (5 / 3 : ℚ) * a_rat j ≤ (5 / 3 : ℚ) * (1 / 2 : ℚ) := by
    have hj2 := a_rat_le_half j hj
    linarith
  have h6 : (5 / 3 : ℚ) * (1 / 2 : ℚ) < 1 := by norm_num
  linarith

lemma frac_part_eq_self (q : ℚ) (h1 : 0 ≤ q) (h2 : q < 1) :
  frac_part q = (q : ℝ) := by
  norm_num [frac_part, true,Int.fract_eq_self.2 ⟨(mod_cast h1: (0:ℝ) ≤q),mod_cast h2⟩]

lemma catalan_reciprocal_sum_frac_eq (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
  frac_part (catalan_reciprocal_sum j k) = (catalan_reciprocal_sum j k : ℝ) := by
  have h1 : 0 ≤ catalan_reciprocal_sum j k := le_of_lt (catalan_reciprocal_sum_pos j k hjk)
  have h2 : catalan_reciprocal_sum j k < 1 := catalan_reciprocal_sum_lt_one j k hj hjk
  exact frac_part_eq_self _ h1 h2

lemma catalan_reciprocal_sum_one_one : catalan_reciprocal_sum 1 1 = 1 := by
  norm_num[catalan_reciprocal_sum ]
  change star _=1
  refine inv_one

lemma frac_part_one_one : frac_part (catalan_reciprocal_sum 1 1) = 0 := by
  norm_num [catalan_reciprocal_sum,frac_part]
  rewrite[a_rat,Int.fract_eq_iff]
  norm_num[a, false,comm]

lemma sum_subset_Icc (j₁ j₂ k₂ : ℕ) (hj : j₁ + 1 ≤ j₂) :
  ∑ i ∈ Finset.Icc j₂ k₂, a_rat i ≤ ∑ i ∈ Finset.Icc (j₁ + 1) k₂, a_rat i := by
  use Finset.sum_le_sum_of_subset_of_nonneg (by gcongr) fun and A B=>(ge_of_eq (by rw [a_rat])).trans' (by bound)

lemma catalan_reciprocal_sum_bound_j (j₁ j₂ k₂ : ℕ) (hj₁ : 2 ≤ j₁) (hj₁_lt_j₂ : j₁ < j₂) (hj₂_le_k₂ : j₂ ≤ k₂) :
  catalan_reciprocal_sum j₂ k₂ < a_rat j₁ := by
  have h1 : j₁ + 1 ≤ j₂ := hj₁_lt_j₂
  have h2 : catalan_reciprocal_sum j₂ k₂ = ∑ i ∈ Finset.Icc j₂ k₂, a_rat i := rfl
  have h3 : ∑ i ∈ Finset.Icc j₂ k₂, a_rat i ≤ ∑ i ∈ Finset.Icc (j₁ + 1) k₂, a_rat i := sum_subset_Icc j₁ j₂ k₂ h1
  have h_le : j₁ ≤ k₂ := le_trans hj₁_lt_j₂.le hj₂_le_k₂
  have h4 : ∑ i ∈ Finset.Icc (j₁ + 1) k₂, a_rat i ≤ (2 / 3 : ℚ) * a_rat j₁ - (2 / 3 : ℚ) * a_rat k₂ := a_rat_sum_bound j₁ k₂ hj₁ h_le
  have hp : 0 < (2 / 3 : ℚ) * a_rat k₂ := by
    have hpos : 0 < a_rat k₂ := a_rat_pos k₂
    linarith
  have h5 : (2 / 3 : ℚ) * a_rat j₁ - (2 / 3 : ℚ) * a_rat k₂ < (2 / 3 : ℚ) * a_rat j₁ := sub_lt_self _ hp
  have h6 : (2 / 3 : ℚ) * a_rat j₁ < a_rat j₁ := by
    have hj1_pos : 0 < a_rat j₁ := a_rat_pos j₁
    linarith
  linarith

lemma catalan_reciprocal_sum_lower_bound (j k : ℕ) (hjk : j ≤ k) :
  a_rat j ≤ catalan_reciprocal_sum j k := by
  simp_rw [catalan_reciprocal_sum, a_rat, ·≤.] at hjk⊢
  exact (Bool.eq_false_iff.2 (show¬_<(_:ℚ)⁻¹ from not_lt.2 (.trans (by rw []) (Finset.single_le_sum (by bound) (by simp_all)))))

lemma catalan_reciprocal_sum_strict_mono_k (j k₁ k₂ : ℕ) (hjk₁ : j ≤ k₁) (hk : k₁ < k₂) :
  catalan_reciprocal_sum j k₁ < catalan_reciprocal_sum j k₂ := by
  simp_rw [catalan_reciprocal_sum,.≤ ·]at*
  delta and a_rat
  norm_num[a, false,← Finset.sum_sdiff (Finset.Icc_subset_Icc_right (@hk).le)]at*
  use Finset.sum_pos' (fun A B=>by positivity) ⟨k₂,by simp_all[(Nat.choose_le_choose _ (by valid:k₂<2*k₂)).trans',hjk₁.trans hk.le]⟩

lemma catalan_reciprocal_sum_inj_k (j k₁ k₂ : ℕ) (hjk₁ : j ≤ k₁) (hjk₂ : j ≤ k₂)
    (h_eq : catalan_reciprocal_sum j k₁ = catalan_reciprocal_sum j k₂) : k₁ = k₂ := by
  simp_rw [catalan_reciprocal_sum,le_antisymm_iff] at *
  delta and a_rat at*
  delta and a at*
  use not_lt.1 fun and=>(( Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right and) fun and I I=>by positivity).trans h_eq.1).not_gt (( Finset.sum_Icc_succ_top (by valid) (_)).ge.trans_lt' ? _)
  · use not_lt.1 fun and=>(h_eq.2.trans_lt ((lt_add_of_pos_right _) @?_)).not_ge.comp ( Finset.sum_Icc_succ_top (by valid) (_)).ge.trans ( Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right and) (by bound) )
    exact (inv_pos.mpr (Nat.cast_pos.mpr (Nat.div_pos ↑(.trans (by norm_num) (Nat.choose_le_choose _ ↑(lt_mul_left k₁.succ_pos (by constructor)))) (by((bound))))))
  · exact (lt_add_of_pos_right _) ((inv_pos.2 (Nat.cast_pos.mpr ↑(Nat.div_pos ↑(.trans (by. (norm_num)) (Nat.choose_le_choose ↑_ ↑(lt_mul_left k₂.succ_pos (by constructor)))) k₂.succ.succ_pos))))

lemma catalan_reciprocal_sum_inj (j₁ k₁ j₂ k₂ : ℕ) (hj₁ : 2 ≤ j₁) (hjk₁ : j₁ ≤ k₁)
    (hj₂ : 2 ≤ j₂) (hjk₂ : j₂ ≤ k₂)
    (h_eq : catalan_reciprocal_sum j₁ k₁ = catalan_reciprocal_sum j₂ k₂) :
  j₁ = j₂ ∧ k₁ = k₂ := by
  have hj_eq : j₁ = j₂ := by
    cases lt_trichotomy j₁ j₂ with
    | inl hlt =>
      have hc1 : catalan_reciprocal_sum j₂ k₂ < a_rat j₁ := catalan_reciprocal_sum_bound_j j₁ j₂ k₂ hj₁ hlt hjk₂
      have hc2 : a_rat j₁ ≤ catalan_reciprocal_sum j₁ k₁ := catalan_reciprocal_sum_lower_bound j₁ k₁ hjk₁
      linarith
    | inr h_or =>
      cases h_or with
      | inl heq => exact heq
      | inr hlt =>
        have hc1 : catalan_reciprocal_sum j₁ k₁ < a_rat j₂ := catalan_reciprocal_sum_bound_j j₂ j₁ k₁ hj₂ hlt hjk₁
        have hc2 : a_rat j₂ ≤ catalan_reciprocal_sum j₂ k₂ := catalan_reciprocal_sum_lower_bound j₂ k₂ hjk₂
        linarith
  subst hj_eq
  have hk_eq : k₁ = k₂ := catalan_reciprocal_sum_inj_k j₁ k₁ k₂ hjk₁ hjk₂ h_eq
  exact ⟨rfl, hk_eq⟩

lemma oeis_108_cases (j k : ℕ) (h : oeis_108_index_cond j k) :
  (j = 1 ∧ k = 1) ∨ (2 ≤ j ∧ j ≤ k) := by
  simp_rw [oeis_108_index_cond, or_iff_not_imp_left] at h⊢
  classical valid

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄, oeis_108_index_cond j₁ k₁ → oeis_108_index_cond j₂ k₂ → (j₁, k₁) ≠ (j₂, k₂) → frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂) := by
  -- EVOLVE-BLOCK-START
  intros j₁ k₁ j₂ k₂ cond1 cond2 h_neq
  have h_cases1 := oeis_108_cases j₁ k₁ cond1
  have h_cases2 := oeis_108_cases j₂ k₂ cond2
  cases h_cases1 with
  | inl h1 =>
    cases h_cases2 with
    | inl h2 =>
      have heq : (j₁, k₁) = (j₂, k₂) := by
        ext
        · simp [h1.1, h2.1]
        · simp [h1.2, h2.2]
      exact False.elim (h_neq heq)
    | inr h2 =>
      have eq1 : frac_part (catalan_reciprocal_sum j₁ k₁) = 0 := by
        rw [h1.1, h1.2]
        exact frac_part_one_one
      have eq2 : frac_part (catalan_reciprocal_sum j₂ k₂) = (catalan_reciprocal_sum j₂ k₂ : ℝ) := catalan_reciprocal_sum_frac_eq j₂ k₂ h2.1 h2.2
      have pos : (0 : ℝ) < (catalan_reciprocal_sum j₂ k₂ : ℝ) := by
        exact mod_cast catalan_reciprocal_sum_pos j₂ k₂ h2.2
      rw [eq1, eq2]
      exact ne_of_lt pos
  | inr h1 =>
    cases h_cases2 with
    | inl h2 =>
      have eq1 : frac_part (catalan_reciprocal_sum j₂ k₂) = 0 := by
        rw [h2.1, h2.2]
        exact frac_part_one_one
      have eq2 : frac_part (catalan_reciprocal_sum j₁ k₁) = (catalan_reciprocal_sum j₁ k₁ : ℝ) := catalan_reciprocal_sum_frac_eq j₁ k₁ h1.1 h1.2
      have pos : (0 : ℝ) < (catalan_reciprocal_sum j₁ k₁ : ℝ) := by
        exact mod_cast catalan_reciprocal_sum_pos j₁ k₁ h1.2
      rw [eq1, eq2]
      exact ne_of_gt pos
    | inr h2 =>
      have eq1 : frac_part (catalan_reciprocal_sum j₁ k₁) = (catalan_reciprocal_sum j₁ k₁ : ℝ) := catalan_reciprocal_sum_frac_eq j₁ k₁ h1.1 h1.2
      have eq2 : frac_part (catalan_reciprocal_sum j₂ k₂) = (catalan_reciprocal_sum j₂ k₂ : ℝ) := catalan_reciprocal_sum_frac_eq j₂ k₂ h2.1 h2.2
      rw [eq1, eq2]
      intro h_eq_real
      have h_eq_rat : catalan_reciprocal_sum j₁ k₁ = catalan_reciprocal_sum j₂ k₂ := by exact mod_cast h_eq_real
      have h_inj : j₁ = j₂ ∧ k₁ = k₂ := catalan_reciprocal_sum_inj j₁ k₁ j₂ k₂ h1.1 h1.2 h2.1 h2.2 h_eq_rat
      have heq : (j₁, k₁) = (j₂, k₂) := by
        ext
        · exact h_inj.1
        · exact h_inj.2
      exact h_neq heq
  -- EVOLVE-BLOCK-END
