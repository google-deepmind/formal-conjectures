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




open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

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
lemma period_of_power_mod_T0_is_period (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
  let T0 := if p ^ 2 ∣ n then n / p else n;
  ∀ k : ℕ, (k + T0) ^ p % n = k ^ p % n := by
  refine fun and=> if a:_ then (if_pos a▸(n.modEq_of_dvd) ? _)else (by·norm_num [a,Nat.pow_mod])
  cases a with simp_all[←geom_sum₂_mul,←CharP.intCast_eq_zero_iff (ZMod p),geom_sum₂_self, mul_dvd_mul,hp.ne_zero,mul_assoc,sq]

lemma period_of_power_mod_T0_le_T (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0)
  (T : ℕ) (hT_pos : T > 0) (hT : ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) :
  (if p ^ 2 ∣ n then n / p else n) ≤ T := by
  refine if a:_ then (if_pos a▸n.div_le_of_le_mul (n.le_of_dvd (p.mul_pos hp.pos (by assumption)) ( (n.factorization_le_iff_dvd fun and=>by simp_all (p.mul_ne_zero hp.ne_zero (by·omega))).1 fun and=>(?_))))else(? _)
  · refine if a:and.Prime then (not_lt.1 fun and' =>absurd (Fact.mk a) fun and' =>absurd (Nat.ModEq.of_dvd (n.ordProj_dvd and) (hT 0)) ? _)else (by norm_num[a])
    obtain ⟨@c⟩ :=eq_or_ne p and
    · simp_all[a.pow_dvd_iff_le_factorization,pos_iff_ne_zero,a.ne_zero,Nat.modEq_zero_iff_dvd]
      simp_all[add_comm 1,add_pow_prime_eq]
      use not_le.1 fun and=>absurd ((pow_dvd_pow p (by valid)).trans (n.ordProj_dvd p)) fun and=>absurd (hT (1)) ?_
      use mt (Nat.ModEq.of_dvd and ·|>.symm.dvd) ?_
      push_cast[mul_one, add_assoc, one_pow, one_mul,add_sub_cancel_left]at*
      rw[dvd_add_right]
      · rw_mod_cast[pow_succ',mul_assoc, mul_dvd_mul_iff_left a.ne_zero,Nat.Coprime.dvd_mul_right]
        · simp_all[a.pow_dvd_iff_le_factorization]
        rw[Nat.coprime_comm, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_Ioo.2 ⟨tsub_pos_of_lt a.one_lt,by cases a.pos with constructor⟩)]
        apply(a.coprime_iff_not_dvd.mpr ((p.dvd_add_left (Finset.dvd_sum fun and x =>?_)).not.mpr (by norm_num[p.sub_sub_self,a.one_le, a.pos, a.ne_one]))).symm.pow_right
        apply((not_imp_comm.1 T.factorization_eq_zero_of_not_dvd (by nlinarith!)).pow (( Finset.mem_sdiff.1 x).elim (by cases Finset.mem_Ioo.1 · with valid ∘mt Finset.mem_singleton.2))).mul_right
      · exact mod_cast(pow_dvd_pow p (by valid)).trans (pow_mul' p _ _▸pow_dvd_pow_of_dvd (T.ordProj_dvd _) _)
    · simp_all[a.pow_dvd_iff_le_factorization,←geom_sum₂_mul_of_ge,pos_iff_ne_zero,hp.ne_zero,Nat.modEq_zero_iff_dvd]
      convert not_le.1 fun and' =>absurd (Nat.ModEq.of_dvd (n.ordProj_dvd and) (hT (1))) ( _)
      norm_num[add_comm, ←geom_sum_mul_neg, false,Nat.modEq_iff_dvd]at*
      use mod_cast not_le.2 ‹_› ∘(a.pow_dvd_iff_le_factorization hT_pos).1 ∘((a.coprime_iff_not_dvd.2 (by valid ∘symm ∘ (and.prime_dvd_prime_iff_eq a hp).1 ∘?_)).pow_left _).dvd_mul_left.1
      induction (by_contra (ne_zero_of_lt (by assumption) ∘eq_bot_mono and' ∘congr_arg ↑( _) ∘T.factorization_eq_zero_of_not_dvd) ) with ·norm_num[←CharP.cast_eq_zero_iff (ZMod and), *]
  · use (if_neg a▸n.le_of_dvd hT_pos ((n.factorization_le_iff_dvd fun and=>by simp_all (by omega)).1 fun and=>not_lt.1 fun and' =>absurd (Nat.ModEq.symm (hT 0)).dvd fun and' =>absurd (hT (1)) ?_))
    use if I:and.Prime then mt (Nat.ModEq.of_dvd (n.ordProj_dvd and)) ?_ else (by norm_num[I]at‹_<_›)
    simp_all[add_comm,sq,Int.natCast_dvd,←geom_sum_mul_neg,hp.ne_zero,Nat.modEq_iff_dvd]
    use mod_cast mt ((I.coprime_iff_not_dvd.2 fun andS=>a (sq p▸?_)).pow_left _).dvd_mul_left.1 (not_le.2 (by valid) ∘(I.pow_dvd_iff_le_factorization (by omega)).1)
    cases (and.prime_dvd_prime_iff_eq I hp).1 (by cases I.dvd_of_dvd_pow ((not_imp_comm.1 n.factorization_eq_zero_of_not_dvd (ne_zero_of_lt (by assumption))).trans and') with·simp_all [←CharP.cast_eq_zero_iff (ZMod and)])
    rcases isEmpty_or_nonempty ℝ
    · norm_num at‹_›
    apply(pow_dvd_pow _ _).trans (n.ordProj_dvd _)
    exact (lt_of_le_of_lt (I.factorization_pos_of_dvd (by·omega) (I.dvd_of_dvd_pow ((not_imp_comm.mp (n : ℕ).factorization_eq_zero_of_not_dvd (and').ne_bot).trans (by assumption))))) (and')

lemma T0_pos (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
  (if p ^ 2 ∣ n then n / p else n) > 0 := by
  refine if a :_ then (if_pos a▸ (p.div_pos (p.le_of_dvd @hn ↑(dvd_of_mul_left_dvd a)) hp.pos))else (if_neg a▸hn)
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) : period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  -- EVOLVE-BLOCK-START
  have h_T0_pos : (if p ^ 2 ∣ n then n / p else n) > 0 := T0_pos p n hp hn
  have h_is_period : ∀ k : ℕ, (k + (if p ^ 2 ∣ n then n / p else n)) ^ p % n = k ^ p % n := period_of_power_mod_T0_is_period p n hp hn
  have h_le_T : ∀ T > 0, (∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) → (if p ^ 2 ∣ n then n / p else n) ≤ T := by
    intro T hT_pos hT
    exact period_of_power_mod_T0_le_T p n hp hn T hT_pos hT
  delta period_of_power_mod abs
  exact (if_neg ↑hn.ne')▸IsLeast.csInf_eq ⟨ (by(trivial)), fun and=>And.elim (@h_le_T _)⟩
  -- EVOLVE-BLOCK-END
