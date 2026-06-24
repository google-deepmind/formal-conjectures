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




open Nat

/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot (2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)

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
def M (n : ℕ) : ℕ := Nat.choose (12 * n + 6) (6 * n + 3) * Nat.choose (6 * n + 3) (4 * n + 2)

lemma M_prop (n : ℕ) : M n * ((6 * n + 3)! * (4 * n + 2)! * (2 * n + 1)!) = (12 * n + 6)! := by
  rw [←eq_comm, M]
  exact (.trans (by rw [←Nat.choose_mul_factorial_mul_factorial (by valid:6*n+3≤ _),←Nat.choose_mul_factorial_mul_factorial (by valid:4*n+2≤_+3)]) (by grind))

lemma main_identity (n : ℕ) :
  ((12 * n + 6)! * (6 * n + 9)!) * (6 * (6 * n + 5) * (6 * n + 4)) =
  (108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2)) * (M n * (6 * n + 7) * (3 * n + 4)) := by
  rw[ M,mul_assoc]
  repeat rw[Nat.choose_eq_factorial_div_factorial (by valid)]
  repeat rw[Nat.div_mul_div_comm (Nat.factorial_mul_factorial_dvd_factorial (by valid)) (Nat.factorial_mul_factorial_dvd_factorial<|by valid)]
  refine (by valid:12*n+6-(6*n+3)=6*n+3).symm▸ (by valid:6*n+3- (4*n+2) =2*n + 1).symm▸(6*n+8).factorial_succ.symm▸(6*n+7).factorial_succ.symm▸?_
  have: (6*n+3)!*( (4*n+2)!*(2*n+1)!) ∣(12*n+6)! := (mul_dvd_mul_left _<|Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (? _)
  · simp_rw [mul_right_comm @_ (( _) +3)!,Nat.mul_div_mul_right _ _ (@Nat.factorial_pos _), (2 *(n)+2).factorial_succ, (2 *n+1).factorial_succ,↑(_+6).factorial_succ,↑(_+5).factorial_succ]at*
    exact (congr_arg (·* _) ((Nat.mul_div_cancel') this).symm).trans ((6*n+4).factorial_succ.symm▸ (@6 *(n)+3).factorial_succ.symm▸ (by ring1))
  · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans ((congr_arg _) (by ring)).dvd

lemma div_6n5 (n : ℕ) : (6 * n + 5) ∣ Nat.choose (12 * n + 6) (6 * n + 3) := by
  have h1 : (6 * n + 5) * Nat.choose (12 * n + 6) (6 * n + 5) = (6 * n + 2) * Nat.choose (12 * n + 6) (6 * n + 4) := by
    exact (.trans (by rw [mul_comm,Nat.choose_succ_right_eq]) ((congr_arg ↑( _) ↑(Nat.sub_eq_of_eq_add (by(((ring)))))).trans (mul_comm _ _)))
  have h2 : (6 * n + 4) * Nat.choose (12 * n + 6) (6 * n + 4) = (6 * n + 3) * Nat.choose (12 * n + 6) (6 * n + 3) := by
    rw [←mul_comm,Nat.choose_succ_right_eq, (by valid:_-_ = 6*n+3),mul_comm]
  have h3 : (6 * n + 5).Coprime (6 * n + 2) := by
    exact (Nat.coprime_self_add_left.2) (Nat.prime_three.coprime_iff_not_dvd.2 (by valid ) )
  have h4 : (6 * n + 5) ∣ (6 * n + 2) * Nat.choose (12 * n + 6) (6 * n + 4) := by
    use Nat.choose (12 * n + 6) (6 * n + 5)
    rw [← h1]
  have h5 : (6 * n + 5) ∣ Nat.choose (12 * n + 6) (6 * n + 4) := by
    exact Nat.Coprime.dvd_of_dvd_mul_left h3 h4
  have h6 : (6 * n + 5).Coprime (6 * n + 3) := by
    exact (Nat.coprime_self_add_left.mpr (Odd.coprime_two_left ⟨ n *3+1,by ·ring⟩))
  have h7 : (6 * n + 5) ∣ (6 * n + 3) * Nat.choose (12 * n + 6) (6 * n + 3) := by
    obtain ⟨c, hc⟩ := h5
    use c * (6 * n + 4)
    calc
      (6 * n + 3) * Nat.choose (12 * n + 6) (6 * n + 3) = (6 * n + 4) * Nat.choose (12 * n + 6) (6 * n + 4) := by rw [h2]
      _ = (6 * n + 4) * ((6 * n + 5) * c) := by rw [hc]
      _ = (6 * n + 5) * (c * (6 * n + 4)) := by ring
  exact Nat.Coprime.dvd_of_dvd_mul_left h6 h7

lemma div_6n4 (n : ℕ) : (6 * n + 4) ∣ Nat.choose (12 * n + 6) (6 * n + 3) := by
  let := (12*n+6).succ_mul_choose_eq (6*n+3)
  exact (Nat.dvd_add_right (↑(this.symm▸dvd_mul_left _ _)) ).mp ⟨2* _,by·linarith only⟩

lemma div_3_choose (n : ℕ) : 3 ∣ Nat.choose (6 * n + 3) (4 * n + 2) := by
  let := (6* n+2).choose_succ_right_eq (4*n+1)
  norm_num[Nat.choose,(by valid:6*n+2-(4*n + 1) =2*n + 1)]at this⊢
  exact (mul_right_cancel₀ (by cases.)) (this.symm.trans (.trans (congr_arg _ (by ring:_=2*(2*n + 1))) ((mul_assoc _ _ _).symm)))▸by valid

lemma div_4_M (n : ℕ) : 4 ∣ M n * (3 * n + 4) := by
  rewrite[mul_add, M]
  norm_num[(by ring:12*n+6=2*(6*n+3)),Nat.choose_mul]
  have := (6 * n+3).choose_succ_right_eq (4 *n+1)
  obtain ⟨a, _⟩ | ⟨a, _⟩ := ( (2 * (6*n+3)).choose (6*n+3)).even_or_odd
  · simp_all[<-two_mul, (by valid:6*n+3- (4*n + 1) =2*n+2),mul_assoc]
    obtain ⟨a, rfl⟩| ⟨a, rfl⟩:=n.even_or_odd
    · refine ⟨ (3) * a*(Nat.choose _ _) * _,by ring⟩
    · exact (mul_dvd_mul_left _) ((((Nat.prime_two.dvd_mul.1 ⟨(a+1)*.choose _ (_+1),mul_left_cancel₀ two_ne_zero (by linear_combination2 this)⟩).resolve_right (by valid : ¬2 ∣2* (2 *a+1)+1)).mul_right _).mul_left _)
  · exact absurd ((by valid:).symm.trans (Nat.choose_mul_right (nofun))) (by valid)

lemma lem_div (n : ℕ) : 6 * (6 * n + 5) * (6 * n + 4) ∣ M n * (6 * n + 7) * (3 * n + 4) := by
  have h1 : (6 * n + 5) ∣ Nat.choose (12 * n + 6) (6 * n + 3) := div_6n5 n
  have h2 : (6 * n + 4) ∣ Nat.choose (12 * n + 6) (6 * n + 3) := div_6n4 n
  have h3 : 3 ∣ Nat.choose (6 * n + 3) (4 * n + 2) := div_3_choose n
  have h4 : 4 ∣ M n * (3 * n + 4) := div_4_M n
  have h_coprime : Nat.Coprime (6 * n + 5) (6 * n + 4) := by
    norm_num[add_comm @_ @1]
  have h5 : (6 * n + 5) * (6 * n + 4) ∣ Nat.choose (12 * n + 6) (6 * n + 3) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h1 h2
  have h6 : 3 * ((6 * n + 5) * (6 * n + 4)) ∣ M n := by
    obtain ⟨a, ha⟩ := h5
    obtain ⟨b, hb⟩ := h3
    use a * b
    calc
      M n = Nat.choose (12 * n + 6) (6 * n + 3) * Nat.choose (6 * n + 3) (4 * n + 2) := rfl
      _ = ((6 * n + 5) * (6 * n + 4) * a) * (3 * b) := by rw [ha, hb]
      _ = 3 * ((6 * n + 5) * (6 * n + 4)) * (a * b) := by ring
  obtain ⟨k, hk⟩ := h6
  have h7 : 4 ∣ 3 * ((6 * n + 5) * (6 * n + 4)) * k * (3 * n + 4) := by
    rw [← hk]
    exact h4
  have h8 : ∃ m, k * (6 * n + 7) * (3 * n + 4) = 2 * m := by
    norm_num[parity_simps, M,← (even_iff_two_dvd),←dvd_def] at hk⊢
    use k.even_or_odd.imp_right (n.not_odd_iff_even.1 ∘fun ⟨a, _⟩⟨x, _⟩=>by norm_num[*, mul_add,<-mul_assoc,(4).dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod] at h7)
  obtain ⟨m, hm⟩ := h8
  use m
  calc
    M n * (6 * n + 7) * (3 * n + 4) = 3 * ((6 * n + 5) * (6 * n + 4)) * k * (6 * n + 7) * (3 * n + 4) := by rw [hk]
    _ = 3 * (6 * n + 5) * (6 * n + 4) * (k * (6 * n + 7) * (3 * n + 4)) := by ring
    _ = 3 * (6 * n + 5) * (6 * n + 4) * (2 * m) := by rw [hm]
    _ = 6 * (6 * n + 5) * (6 * n + 4) * m := by ring
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : 108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!) ^ 2) ∣ (12 * n + 6)! * (6 * n + 9)! := by
  -- EVOLVE-BLOCK-START
  have h1 := main_identity n
  have h2 := lem_div n
  obtain ⟨k, hk⟩ := h2
  have h3 : ((12 * n + 6)! * (6 * n + 9)!) * (6 * (6 * n + 5) * (6 * n + 4)) =
            (108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2) * k) * (6 * (6 * n + 5) * (6 * n + 4)) := by
    calc
      ((12 * n + 6)! * (6 * n + 9)!) * (6 * (6 * n + 5) * (6 * n + 4))
        = 108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2) * (M n * (6 * n + 7) * (3 * n + 4)) := h1
      _ = 108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2) * (6 * (6 * n + 5) * (6 * n + 4) * k) := by rw [hk]
      _ = (108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2) * k) * (6 * (6 * n + 5) * (6 * n + 4)) := by ring
  have h4 : 6 * (6 * n + 5) * (6 * n + 4) > 0 := by
    bound
  have h5 : (12 * n + 6)! * (6 * n + 9)! = 108 * ((4 * n + 2)! * (2 * n + 3)! * (6 * n + 5)!^2) * k := by
    exact (Nat.mul_right_cancel h4) @h3
  exact ⟨k, h5⟩
  -- EVOLVE-BLOCK-END
