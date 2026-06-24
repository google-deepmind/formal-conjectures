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
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.
-/
def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0

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
lemma choose_double_even (j : ℕ) (hj : j > 0) : (2 * j).choose j % 2 = 0 := by
  rwa [Nat.choose_mul_right ∘ne_zero_of_lt,Nat.mul_mod_right]

lemma fixed_point_term_even (n j : ℕ) (hj : j > 0) :
    (n.choose j * (n + j).choose j) % 2 = 0 := by
  rw [←Nat.even_iff,n.add_choose_eq,gt_iff_lt] at*
  simp_all[j.choose_symm (Finset.mem_range_succ_iff.1 _),mul_left_comm,pos_iff_ne_zero, Finset.mul_sum, Finset.Nat.antidiagonal_eq_map]
  refine if a:j ≤n then (by_contra fun and=> absurd (j.sum_range_choose▸ Finset.mul_sum _ _ (n.choose j)) ? _)else⟨0,by simp_all[n.choose_eq_zero_of_lt]⟩
  replace a : ∀ a ∈ Finset.range (j+1),n.choose j*(n.choose a*(j.choose a)) % 2 =n.choose j*j.choose a%2:= fun and x =>?_
  · use and ∘Nat.even_iff.2.comp (by rw [ Finset.sum_nat_mod, Finset.sum_congr rfl a,← Finset.sum_nat_mod,←.,((dvd_pow_self (2 : ℕ) (hj)).mul_left _).modEq_zero_nat])
  · simp_all[mul_left_comm (n.choose j),n.choose_mul,Nat.mod_two_of_bodd, and.lt_succ]

lemma choose_identity (n k j : ℕ) (h : k ≤ n) :
    n.choose k * (n + j).choose j = (k + j).choose k * (n + j).choose (n - k) := by
  simp_all only [le_self_add, true,Nat.choose_mul,Nat.choose_symm_of_eq_add (by valid: n+j= n-k+(k+j)),Nat.add_sub_cancel_left, true, ← n.choose_symm_add, mul_comm]
  rwa [mul_comm _,Nat.choose_mul (by valid),n.sub_add_comm _,Nat.choose_symm_add]

noncomputable def trips (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Iic m) ×ˢ (Finset.Iic m) ×ˢ (Finset.Iic m)).filter fun ⟨n, k, j⟩ =>
    n * (k + 1) + j * (n + 1) = m ∧ k ≤ n

def sigma (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.2.1 + t.2.2, t.2.1, t.1 - t.2.1)

def term (t : ℕ × ℕ × ℕ) : ℕ :=
  t.1.choose t.2.1 * (t.1 + t.2.2).choose t.2.2

lemma sigma_trips {m : ℕ} (t : ℕ × ℕ × ℕ) (ht : t ∈ trips m) : sigma t ∈ trips m := by
  change t ∈ {s |_} at ht⊢
  simp_all[trips,sigma]
  use⟨by nlinarith,by valid⟩,ht.2.1▸by linear_combination(t.2.2+_+1)*.add_sub_of_le ht.2.2

lemma sigma_invol {m : ℕ} (t : ℕ × ℕ × ℕ) (ht : t ∈ trips m) : sigma (sigma t) = t := by
  change t ∈ {s |_}at @ht
  simp_all[trips,sigma]

lemma term_sigma {m : ℕ} (t : ℕ × ℕ × ℕ) (ht : t ∈ trips m) : term (sigma t) = term t := by
  delta term sigma
  change t ∈{s |_}at *
  norm_num[trips,mul_comm (t.1.choose _),add_right_comm t.2.1 t.2.2]at*
  simp_all only[mul_comm ((t.2.1+_).choose _),le_self_add,Nat.choose_mul,Nat.add_sub_of_le,Nat.choose_symm_of_eq_add (t.1.sub_add_cancel ht.2.2▸add_assoc _ _ _),Nat.add_sub_cancel_left,Nat.choose_symm_add]
  simp_all only[<-t.1.choose_symm_add,Nat.sub_add_comm,Nat.choose_mul,le_add_self,Nat.add_sub_cancel,Nat.choose_symm_add]

lemma sum_mod_two_involution {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℕ) (sig : α → α)
    (h_sigma : ∀ a ∈ s, sig a ∈ s)
    (h_invol : ∀ a ∈ s, sig (sig a) = a)
    (h_f : ∀ a ∈ s, f (sig a) = f a) :
    (∑ a ∈ s, f a) % 2 = (∑ a ∈ s.filter (fun a => sig a = a), f a) % 2 := by
  refine s.strongInductionOn ↑(? _) h_invol h_f @h_sigma
  use fun and R M A B=>and.eq_empty_or_nonempty.elim (by bound) (fun ⟨a, _⟩=>.trans (by rw [← (and.add_sum_erase f (by valid))]) (.symm (.trans (by rw [ Finset.sum_filter,← (and.add_sum_erase _) (by valid)]) ?_)))
  refine if I:_ then (if_pos I▸by rw [Nat.ModEq.add_left _ (((R _) (and.erase_ssubset (by valid)) (M · ∘ (and.erase_subset a ·)) (A · ∘ (and.erase_subset a ·)) (by grind)).trans (by rw [ Finset.sum_filter]))])else ?_
  rw [← Finset.sum_erase_add _ _ (and.mem_erase.2 ⟨I,by apply_rules⟩),← Finset.sum_erase_add _ _ (and.mem_erase.2 ⟨I, B a (by valid)⟩),if_neg I, zero_add]
  exact (.trans (by rw [← Finset.sum_filter, if_neg (by rwa[M a (by valid),eq_comm])]) (by_contra (absurd (R (( (and.erase a)).erase (sig a)) ∘(Finset.erase_subset _ _).trans_ssubset ∘and.erase_ssubset) ∘by grind)))

lemma a_mod_2 (m : ℕ) :
    (a m).natAbs % 2 = (∑ t ∈ trips m, term t) % 2 := by
  push_cast [term, a, false, ←Int.natCast_inj]
  trans(∑ a ∈.range (m+1),∑n ∈.range (m+1),ite (a* (n + 1)≤ m) (ite (a+1 ∣m-a* (n + 1)) (-1) 0*a.choose n*(a+(m-a* (n + 1))/(a+1)).choose ((m-a* (n + 1))/(a+1)):ℤ) (0))%2
  · trans(∑ a ∈.range (m+1),∑n ∈.range (a+1),ite (a* (n + 1)≤ m) (ite ( a+1 ∣ m-a* (n + 1)) ((-1) * a.choose n * ( a +(m-a * (n + 1))/(a+1)).choose (@(m-a* (n + 1)) / (a + 1)) : ℤ) (0)) 00)%2
    · norm_num[Int.even_iff, Finset.sum_ite]
      norm_num[←{ a ∈{ a ∈ Finset.range (m+1)|a*(a+1)≤ m}|a+1 ∣m-a*(a+1)}.sum_filter_add_sum_filter_not fun and=>Even ((m-a*(and + 1))/(a+1)), Finset.sum_add_distrib]
      use symm<|.trans (by rw [←funext fun and=> Finset.sum_filter_add_sum_filter_not _ (fun n=>Even ((m-and* (n + 1))/ (and+1))) _, Finset.sum_add_distrib]) @?_
      exact (.trans (by rw [funext fun and=>congr_arg₂ _ (Finset.filter_congr fun and j=>Nat.not_even_iff_odd) rfl]) (.symm (.trans (by rw [abs]) (by valid))))
    · exact (congr_arg) ( ·%2) ( Finset.sum_congr ↑rfl @fun a s =>.trans (congr_arg ↑_ (by ·simp_rw [ite_mul,zero_mul,])) (Finset.sum_subset ↑(by simp_all[a.succ_le]) fun and I I =>a.choose_eq_zero_of_lt (not_lt.mp (I.comp (List.mem_range.mpr)))▸by(((omega)))))
  show @_=(∑ a ∈ { a ∈_|_ }, _)%2
  push_cast only[m.range_succ_eq_Icc_zero,ite_mul,zero_mul,mul_assoc, one_mul, Finset.sum_filter, Finset.sum_product]
  refine(Finset.sum_int_mod _ _ _).trans.comp (congr_arg (.%2) (congr_arg _ (funext fun and=>.trans ( Finset.sum_int_mod _ _ _) ( ((congr_arg₂ _) (Finset.sum_congr (rfl) ? _) rfl ).trans ( Finset.sum_int_mod _ _ _).symm)))).trans ( Finset.sum_int_mod _ _ _).symm
  use fun K V=> if a:_ then (if_pos a▸ if I:_ then (if_pos I▸? _)else (if_neg I▸by rw [ Finset.sum_eq_zero fun and X=>if_neg (I ∘by bound)]))else (if_neg a▸? _)
  · simp_all[mul_comm _ (and+1), (Nat.div_le_self _ _).trans, and.choose_eq_zero_of_lt,←two_mul,←eq_tsub_iff_add_eq_of_le,Int.emod_eq_emod_iff_emod_sub_eq_zero,ite_and]
    cases lt_or_ge and K with cases I with norm_num[*, and.choose_eq_zero_of_lt,←eq_tsub_iff_add_eq_of_le _,add_comm (and* _),(Nat.succ_mul _ _▸le_add_self).trans (@‹_›▸(m.sub_le _))]
  · rw [ Finset.sum_eq_zero (by valid)]

lemma fixed_points_even (m : ℕ) (h_not_form : ∀ n, m ≠ n * (n + 1)) :
    ∀ t ∈ (trips m).filter (fun t => sigma t = t), term t % 2 = 0 := by
  intro t ht
  rw [Finset.mem_filter] at ht
  rcases ht with ⟨ht_trips, ht_fixed⟩
  rcases t with ⟨n, k, j⟩
  have h_trips_cond : n * (k + 1) + j * (n + 1) = m ∧ k ≤ n := by
    rw [trips, Finset.mem_filter] at ht_trips
    exact ht_trips.2
  have hk_le : k ≤ n := h_trips_cond.2
  have h_eq_n : k + j = n := by
    have h1 : (sigma (n, k, j)).1 = (n, k, j).1 := by rw [ht_fixed]
    exact h1
  have hm : n * (k + 1) + j * (n + 1) = m := h_trips_cond.1
  have hm_form : n * (n + 1) + j = m := by
    calc
      n * (n + 1) + j = n * n + n + j := by ring
      _ = (k + j) * n + n + j := by rw [h_eq_n]
      _ = k * n + j * n + n + j := by ring
      _ = n * (k + 1) + j * (n + 1) := by ring
      _ = m := hm
  have hj : j > 0 := by
    by_contra h_j0
    have : j = 0 := by omega
    have : m = n * (n + 1) := by omega
    exact h_not_form n this
  have h_term : term (n, k, j) = n.choose j * (n + j).choose j := by
    unfold term
    dsimp
    have : k = n - j := by omega
    rw [this]
    congr 1
    exact Nat.choose_symm (by omega)
  rw [h_term]
  exact fixed_point_term_even n j hj

lemma sum_even_of_all_even {α : Type} (s : Finset α) (f : α → ℕ) (h : ∀ x ∈ s, f x % 2 = 0) :
    (∑ x ∈ s, f x) % 2 = 0 := by
  push_cast[s.sum_nat_mod, false, (s.sum_eq_zero h)]
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
  -- EVOLVE-BLOCK-START
  intro h_odd
  by_contra h_not
  push_neg at h_not
  have h1 : (a m).natAbs % 2 = 1 := by
    exact (Nat.odd_iff.mp) (h_odd).natAbs
  have h2 : (∑ t ∈ trips m, term t) % 2 = 1 := by
    rw [← a_mod_2 m]
    exact h1
  have h3 : (∑ t ∈ (trips m).filter (fun t => sigma t = t), term t) % 2 = 1 := by
    have := sum_mod_two_involution (trips m) term sigma
      (fun t ht => sigma_trips t ht)
      (fun t ht => sigma_invol t ht)
      (fun t ht => term_sigma t ht)
    rwa [← this]
  have h4 : ∀ t ∈ (trips m).filter (fun t => sigma t = t), term t % 2 = 0 :=
    fixed_points_even m h_not
  have h5 : (∑ t ∈ (trips m).filter (fun t => sigma t = t), term t) % 2 = 0 :=
    sum_even_of_all_even _ _ h4
  rw [h5] at h3
  contradiction
  -- EVOLVE-BLOCK-END
