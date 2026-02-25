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
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)
-/

open Nat Pointwise

namespace Erdos125

open Topology

def S3 : Set ℕ := {x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}}
def S4 : Set ℕ := {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}}

lemma s3_bound (k : ℕ) (x : ℕ) (h : x ∈ S3) (hk : x < 3^k) : x ≤ (3^k - 1) / 2 := by
  rewrite[Nat.le_div_iff_mul_le (by decide),mul_two,Nat.le_sub_one_iff_lt hk.pos, S3]at *
  induction k generalizing x with|zero =>omega|succ =>_
  use not_le.1 fun and=>absurd (‹∀ A B C,_› (x/3) (by simp_all[ (by valid:x>0), Finset.insert_subset_iff])) (by cases show x%3=0 ∨x%3=1by simp_all[ (by valid:x>0), Finset.insert_subset_iff] with valid)

lemma s4_bound (m : ℕ) (y : ℕ) (h : y ∈ S4) (hm : y < 4^m) : y ≤ (4^m - 1) / 3 := by
  norm_num [←geom_sum_mul_of_one_le, S4] at h
  induction m generalizing y with|zero=>omega| succ=>_
  use not_lt.1 fun and=>absurd (‹∀ a s C,a≤_› (y/4) (by simp_all[ Finset.insert_subset_iff,and.pos])) (by cases show y%4=0 ∨y%4=1by simp_all[ Finset.insert_subset_iff,and.pos] with valid)

lemma gap_exists (k m : ℕ) (h : (3^k - 1) / 2 + (4^m - 1) / 3 < min (3^k) (4^m)) :
  ∀ x ∈ S3, ∀ y ∈ S4, ¬ ((3^k - 1) / 2 + (4^m - 1) / 3 < x + y ∧ x + y < min (3^k) (4^m)) := by
  intros x hx y hy h_contra
  have h_x_cases : x < 3^k ∨ 3^k ≤ x := by apply lt_or_le
  have h_y_cases : y < 4^m ∨ 4^m ≤ y := by apply lt_or_ge
  cases h_x_cases with
  | inl hx_lt =>
    cases h_y_cases with
    | inl hy_lt =>
      have hx_bound := s3_bound k x hx hx_lt
      have hy_bound := s4_bound m y hy hy_lt
      valid
    | inr hy_ge =>
      omega
  | inr hx_ge =>
    omega

lemma zero_in_S3 : 0 ∈ S3 := by
  norm_num[ S3]

lemma zero_in_S4 : 0 ∈ S4 := by
  norm_num [S4]

lemma zero_in_S3_add_S4 : 0 ∈ S3 + S4 := by
  have h3 := zero_in_S3
  have h4 := zero_in_S4
  simp_all[Set.mem_add,Exists.intro 0]

lemma one_in_S3 : 1 ∈ S3 := by
  norm_num[ S3]

lemma one_in_S4 : 1 ∈ S4 := by
  norm_num[S4]

lemma two_in_S3_add_S4 : 2 ∈ S3 + S4 := by
  have h3 := one_in_S3
  have h4 := one_in_S4
  constructor
  use h3,1

lemma gap_formula_eval : (3^4 - 1) / 2 + (4^3 - 1) / 3 < min (3^4) (4^3) := by
  try decide

lemma specific_gap_exists : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (61 < x + y ∧ x + y < 64) := by
  have h_eval := gap_formula_eval
  have h_gap := gap_exists 4 3 h_eval
  valid

lemma gap_formula_eval_2 : (3^5 - 1) / 2 + (4^4 - 1) / 3 < min (3^5) (4^4) := by
  focus decide

lemma specific_gap_exists_2 : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (206 < x + y ∧ x + y < 243) := by
  have h_eval := gap_formula_eval_2
  have h_gap := gap_exists 5 4 h_eval
  valid

lemma gap_formula_eval_3 : (3^6 - 1) / 2 + (4^5 - 1) / 3 < min (3^6) (4^5) := by
  focus decide

lemma specific_gap_exists_3 : ∀ x ∈ S3, ∀ y ∈ S4, ¬ (705 < x + y ∧ x + y < 729) := by
  have h_eval := gap_formula_eval_3
  have h_gap := gap_exists 6 5 h_eval
  classical assumption

def KM_seq : ℕ → ℕ × ℕ
| 0 => (5, 4)
| n + 1 =>
  let K := (KM_seq n).1
  let M := (KM_seq n).2
  if 3^K ≤ 4^M then (K + 24, M + 19) else (K + 5, M + 4)

def K_seq (n : ℕ) : ℕ := (KM_seq n).1
def M_seq (n : ℕ) : ℕ := (KM_seq n).2

lemma KM_seq_step_le (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) (h3 : 3^K ≤ 4^M) :
  15 * 3^(K + 24) ≤ 17 * 4^(M + 19) ∧ 5 * 4^(M + 19) ≤ 6 * 3^(K + 24) := by
  have e1 : 3^(K + 24) = 282429536481 * 3^K := by ring!
  have e2 : 4^(M + 19) = 274877906944 * 4^M := by ring
  omega

lemma KM_seq_step_gt (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) (h3 : ¬ (3^K ≤ 4^M)) :
  15 * 3^(K + 5) ≤ 17 * 4^(M + 4) ∧ 5 * 4^(M + 4) ≤ 6 * 3^(K + 5) := by
  have e1 : 3^(K + 5) = 243 * 3^K := by ring1
  have e2 : 4^(M + 4) = 256 * 4^M := by ring
  omega

lemma KM_seq_inv (n : ℕ) : 15 * 3^(K_seq n) ≤ 17 * 4^(M_seq n) ∧ 5 * 4^(M_seq n) ≤ 6 * 3^(K_seq n) := by
  induction n with
  | zero => trivial
  | succ n ih => simp_all![pow_add, K_seq, M_seq, ←mul_assoc]
                 split
                 · field_simp only [pow_add, mul_le_mul',←mul_assoc, and_self]
                   exact ih.elim (mod_cast (by valid))
                 · repeat use pow_add (3) _ _▸pow_add 4 _ _▸by linarith

lemma a_growth (n : ℕ) : n < (3^(K_seq n) - 1) / 2 + (4^(M_seq n) - 1) / 3 := by
  push_cast[ ←geom_sum_mul_of_one_le, K_seq, M_seq, true,n.lt_iff_add_one_le]
  delta Erdos125.KM_seq
  use le_add_right ((Nat.mul_div_cancel _) two_pos▸.trans (?_) ( Finset.sum_le_sum fun and p=>Nat.pow_pos (by decide)))
  use Finset.card_eq_sum_ones ( _)▸(Finset.card_range _)▸n.rec (by decide) fun and p=>show _≤Prod.fst (ite _ _ _)by bound

lemma gap_ineq (K M : ℕ) (h1 : 15 * 3^K ≤ 17 * 4^M) (h2 : 5 * 4^M ≤ 6 * 3^K) :
  10 * ((3^K - 1) / 2 + (4^M - 1) / 3) ≤ 9 * min (3^K) (4^M) := by
  omega

noncomputable def density_seq (A : Set ℕ) (n : ℕ) : ℝ :=
  ((A ∩ Set.univ).interIio n).ncard / (n : ℝ)

lemma has_density_iff (A : Set ℕ) (α : ℝ) :
  A.HasDensity α ↔ Filter.Tendsto (density_seq A) Filter.atTop (𝓝 α) := by
  rw [←tendsto_sub_nhds_zero_iff,Set.HasDensity]
  norm_num[density_seq,tendsto_sub_nhds_zero_iff,Set.partialDensity]

lemma gap_density_eq (A : Set ℕ) (a b : ℕ) (h_gap : ∀ x ∈ A, ¬ (a < x ∧ x < b)) (h_lt : a < b) :
  ((A ∩ Set.univ).interIio b).ncard = ((A ∩ Set.univ).interIio (a + 1)).ncard := by
  exact (congr_arg _) ((Set.ext fun and=>and_congr_right fun and' =>Set.mem_Ioi.trans (.trans (by_contra (h_gap and and'.1 ∘by valid)) (Set.mem_Ioi).symm)))

lemma gap_density_le (A : Set ℕ) (a b : ℕ) (h_gap : ∀ x ∈ A, ¬ (a < x ∧ x < b)) (h_lt : a < b) (h_ratio : 10 * a ≤ 9 * b) :
  density_seq A b ≤ density_seq A (a + 1) * (0.9 + 1 / (b : ℝ)) := by
  push_cast only[density_seq, one_div, not_and_or]at*
  field_simp [h_lt.pos.ne',Set.interIio,div_le_div_iff₀,h_lt.pos]at*
  use(mul_le_mul (mod_cast Nat.card_mono (.of_fintype _) fun R L=> L.imp_right (R.lt_succ_of_le ∘(h_gap R L.1).resolve_right ∘not_le_of_lt)) ?_ (by bound) (by bound)).trans (mul_assoc _ _ _).ge
  linear_combination b/10*(mod_cast (by assumption): (10 * a : ℝ) ≤9 * ↑b)

lemma limit_bounds (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : Filter.Tendsto f Filter.atTop (𝓝 α)) :
  ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α := by
  apply (h_lim.eventually.comp (Icc_mem_nhds ↑(mul_lt_of_lt_one_left h_pos (by ·norm_num))) ↑(lt_mul_left h_pos (by ·norm_num))).exists_forall_of_atTop

lemma contradiction_from_bounds (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_bounds : ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α)
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ f b ≤ f (a + 1) * (0.9 + 1 / (b : ℝ))) :
  False := by
  rcases h_bounds with ⟨N0, h_bound⟩
  have h_ex : ∃ a b, max N0 100 < a ∧ a < b ∧ f b ≤ f (a + 1) * (0.9 + 1 / (b : ℝ)) := h_gap (max N0 100)
  rcases h_ex with ⟨a, b, ha, hab, h_ineq⟩
  have ha1 : N0 ≤ a + 1 := by omega
  have hb : N0 ≤ b := by valid
  have h_fb_lower : 0.99 * α ≤ f b := (h_bound b hb).1
  have h_fa_upper : f (a + 1) ≤ 1.01 * α := (h_bound (a + 1) ha1).2
  have h_b_large : 1 / (b : ℝ) ≤ 0.01 := by linear_combination (one_div_lt_one_div_of_lt (by norm_num)) (mod_cast (by valid):100<(b:ℝ))
  have h_fa_pos : 0 ≤ f (a + 1) := by field_simp only [ (h_bound _ _).1.trans']
  have h_factor : 0.9 + 1 / (b : ℝ) ≤ 0.91 := by linear_combination h_b_large
  have h_fb_upper : f b ≤ 1.01 * α * 0.91 := by use h_ineq.trans (mul_le_mul (by valid) h_factor (by positivity) (by valid))
  have h_contra : 0.99 * α ≤ 0.9191 * α := by bound
  have h_false : False := by linarith
  exact h_false

lemma limit_contradiction (f : ℕ → ℝ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : Filter.Tendsto f Filter.atTop (𝓝 α))
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ f b ≤ f (a + 1) * (0.9 + 1 / (b : ℝ))) :
  False := by
  have h_bounds : ∃ N0, ∀ n ≥ N0, 0.99 * α ≤ f n ∧ f n ≤ 1.01 * α := limit_bounds f α h_pos h_lim
  exact contradiction_from_bounds f α h_pos h_bounds h_gap

lemma contradiction_from_limit (A : Set ℕ) (α : ℝ) (h_pos : 0 < α)
  (h_lim : A.HasDensity α)
  (h_gap : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ A, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b) :
  False := by
  have h_lim' : Filter.Tendsto (density_seq A) Filter.atTop (𝓝 α) := (has_density_iff A α).mp h_lim
  apply limit_contradiction (density_seq A) α h_pos h_lim'
  intro N0
  rcases h_gap N0 with ⟨a, b, h_N0, h_ab, h_empty, h_ratio⟩
  use a, b
  refine ⟨h_N0, h_ab, ?_⟩
  exact gap_density_le A a b h_empty h_ab h_ratio

lemma no_pos_density_of_gaps (A : Set ℕ)
  (h : ∀ N0, ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ A, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b) :
  ¬ A.HasPosDensity := by
  intro h_pos_den
  rcases h_pos_den with ⟨α, h_pos, h_den⟩
  exact contradiction_from_limit A α h_pos h_den h

lemma gap_exists_helper (K M : ℕ) (a b : ℕ) (ha : a = (3^K - 1) / 2 + (4^M - 1) / 3)
  (hb : b = min (3^K) (4^M)) (h_lt : a < b) :
  ∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b) := by
  intro x hx
  have h_ex : ∃ s3 ∈ S3, ∃ s4 ∈ S4, s3 + s4 = x := hx
  rcases h_ex with ⟨s3, h_s3, s4, h_s4, rfl⟩
  subst ha hb
  exact gap_exists K M h_lt s3 h_s3 s4 h_s4

lemma no_pos_density_of_S3_S4_help (N0 : ℕ) :
  ∃ a b, N0 < a ∧ a < b ∧ (∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b)) ∧ 10 * a ≤ 9 * b := by
  let K := K_seq N0
  let M := M_seq N0
  let a := (3^K - 1) / 2 + (4^M - 1) / 3
  let b := min (3^K) (4^M)
  use a, b
  have h_inv := KM_seq_inv N0
  have h1 : N0 < a := a_growth N0
  have h4 : 10 * a ≤ 9 * b := gap_ineq K M h_inv.1 h_inv.2
  have hb_pos : 0 < b := by positivity
  have h2 : a < b := by omega
  have h3 : ∀ x ∈ S3 + S4, ¬ (a < x ∧ x < b) := gap_exists_helper K M a b rfl rfl h2
  exact ⟨h1, h2, h3, h4⟩

lemma density_zero_of_S3_S4 : ¬ (S3 + S4).HasPosDensity := by
  apply no_pos_density_of_gaps (S3 + S4)
  intro N0
  exact no_pos_density_of_S3_S4_help N0

/-
Let $A = {∑ ε_{k} 3^{k} : ε_{k} ∈ {0,1}}$ be the set of integers which
have only the digits $0, 1$ when written base 3, and $B = {∑ ε_{k} 4^{k} : ε_{k} ∈ {0,1}}$
be the set of integers which have only the digits $0, 1$ when written base 4.
Does $A + B$ have positive density?
-/

@[category research solved, AMS 11]
theorem erdos_125 :
    answer(False) ↔ ({ x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }).HasPosDensity := by
  have h : ¬ ({x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1}}).HasPosDensity := by
    exact density_zero_of_S3_S4
  symm
  exact iff_false_intro h

end Erdos125
