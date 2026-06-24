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




open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def r_const : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def r_sq : ℝ := r_const * r_const

/--
A341254: $a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := r_const
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

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
noncomputable def m_val (n : ℕ) : ℤ := Int.floor ((n : ℝ) * r_const)
noncomputable def eps (n : ℕ) : ℝ := (n : ℝ) * r_const - m_val n
noncomputable def I_val (n : ℕ) : ℤ := 2 * m_val n + (n / 4 : ℕ)

lemma r_sq_eq : r_sq = 2 * r_const + 1 / 4 := by
  norm_num only[r_const,r_sq]
  linear_combination .mul_self_sqrt (@5:).cast_nonneg/4

lemma a_val (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = (Int.floor (r_const * (m_val n : ℝ)) : ℝ) := by
  delta m_val a r_const
  exact (Int.cast_natCast _).symm.trans (by rw [Int.toNat_of_nonneg (by positivity),mul_comm (n: ℝ)])

lemma eps_bounds (n : ℕ) (hn : 1 ≤ n) : 0 < eps n ∧ eps n < 1 := by
  simp_rw [eps,·≤·]at*
  norm_num[r_const, true,m_val]at *
  exact ⟨Int.fract_pos.2 ((Nat.prime_five.irrational_sqrt ⟨⌊↑n*((2+√5)/2)⌋/n*2-2,by simp_all[←.,n.one_le_iff_ne_zero]⟩)),Int.fract_lt_one _,⟩

lemma r_bound : (-1 / 4 : ℝ) < 2 - r_const ∧ 2 - r_const < 0 := by
  norm_num only[r_const,lt_sub_comm, sub_neg]
  norm_num[div_eq_mul_inv, add_lt_of_lt_sub_left,←sub_lt_iff_lt_add',←lt_div_iff₀,←div_lt_iff₀,Real.sqrt_lt,Real.lt_sqrt]

lemma n_div_4 (n : ℕ) : (n : ℝ) / 4 = ( (n / 4 : ℕ) : ℝ) + ( (n % 4 : ℕ) : ℝ) / 4 := by
  exact (.trans (by rw [← n.div_add_mod @4, Nat.cast_add, Nat.cast_mul]) (by·ring))

lemma r_m_eq (n : ℕ) : r_const * (m_val n : ℝ) = (I_val n : ℝ) + ( (n % 4 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n := by
  norm_num[r_const, I_val, sub_mul,eps, true,m_val]
  exact (symm (.trans (by rw [Nat.mod_def,Nat.cast_sub (n.mul_div_le _),Nat.cast_mul _,Int.fract]) (by linear_combination(norm:=ring!)-.sq_sqrt (5).cast_nonneg/4*n)))

lemma n_r_sq_eq (n : ℕ) : (n : ℝ) * r_sq = (I_val n : ℝ) + ( (n % 4 : ℕ) : ℝ) / 4 + 2 * eps n := by
  norm_num[r_sq, I_val, false,eps, true, (n : ℕ).mod_def _]
  norm_num[r_const, sub_div, mul_sub, add_assoc,mul_left_comm,n.mul_div_le,←sq]
  linear_combination(norm:=ring!).sq_sqrt (5).cast_nonneg/4*n

lemma floor_case_0 (x : ℝ) (hx1 : -1/4 < x) (hx2 : x < 0) : (Int.floor x : ℝ) = -1 := by
  exact (mod_cast (by norm_num[Int.floor_eq_iff,hx1.le.trans', *]))

lemma floor_case_1 (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) : (Int.floor x : ℝ) = 0 := by
  push_cast[eq_self,Int.floor_eq_zero_iff.2 (by use hx1)]

lemma int_add_floor (z : ℤ) (x : ℝ) : (Int.floor ((z : ℝ) + x) : ℝ) = (z : ℝ) + (Int.floor x : ℝ) := by
  simp_all
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : 1 ≤ n) : (1 / 4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧ (n : ℝ) * r_sq - (a n : ℝ) < 3 := by
  -- EVOLVE-BLOCK-START
  have he := eps_bounds n hn
  have hr := r_bound
  have ha := a_val n hn
  have hrm := r_m_eq n
  have hnsq := n_r_sq_eq n
  have h_int := int_add_floor (I_val n) (((n % 4 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n)

  have eq1 : (a n : ℝ) = (I_val n : ℝ) + (Int.floor (((n % 4 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n) : ℝ) := by
    rwa [ha, hrm, add_assoc]

  have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega

  rcases h_mod with h0 | h1 | h2 | h3
  · have h_bounds : -1/4 < (2 - r_const) * eps n ∧ (2 - r_const) * eps n < 0 := by use hr.1.trans (lt_mul_of_lt_one_right hr.2 he.right), mul_neg_of_neg_of_pos hr.2 he.1
    have h_floor : (Int.floor (((0 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n) : ℝ) = -1 := by exact (mod_cast (by norm_num [Int.floor_eq_iff,h_bounds.1.le.trans', *]))
    repeat use by nlinarith only[hr, he,h0▸hnsq,h0▸eq1,h_floor]
  · have h_bounds : 0 ≤ ((1 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n ∧ ((1 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n < 1 := by use (by linear_combination mul_lt_mul_of_neg_left he.2 hr.2+hr.1),by linear_combination mul_neg_of_neg_of_pos hr.2 he.1
    have h_floor : (Int.floor (((1 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n) : ℝ) = 0 := by rwa[Int.floor_eq_zero_iff.2, Int.cast_zero]
    repeat use (@hnsq▸eq1▸h1.symm▸h_floor▸by. (linarith only[he]))
  · have h_bounds : 0 ≤ ((2 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n ∧ ((2 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n < 1 := by repeat use by nlinarith only[hr, he]
    have h_floor : (Int.floor (((2 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n) : ℝ) = 0 := by rwa [Int.floor_eq_zero_iff.2, Int.cast_zero]
    repeat use hnsq▸eq1▸h2.symm▸h_floor▸by linarith only[he]
  · have h_bounds : 0 ≤ ((3 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n ∧ ((3 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n < 1 := by use (by nlinarith),by nlinarith
    have h_floor : (Int.floor (((3 : ℕ) : ℝ) / 4 + (2 - r_const) * eps n) : ℝ) = 0 := by rwa [Int.floor_eq_zero_iff.mpr, Int.cast_zero]
    repeat use eq1▸hnsq▸h3.symm▸h_floor▸by linarith only[he]
  -- EVOLVE-BLOCK-END
