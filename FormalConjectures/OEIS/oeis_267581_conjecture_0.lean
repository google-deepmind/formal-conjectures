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




open Nat Int

/-- The rule function for Rule 167. Inputs must be 0 or 1. -/
def ca_rule_167 (c_L c_C c_R : ℕ) : ℕ :=
  let R : ℕ := 167
  let index : ℕ := 4 * c_L + 2 * c_C + c_R
  -- Rule 167 is determined by the index-th bit of R.
  (R / (2 ^ index)) % 2

/--
The state of the Rule 167 elementary cellular automaton at time $t$ and position $x$.
The initial condition is a single ON cell at $x=0$.
$C(t, x)$ is structurally recursive on $t$.
-/
def ca_state (t : ℕ) (x : ℤ) : ℕ :=
  match t with
  | 0 => if x = 0 then 1 else 0
  | t' + 1 =>
    let C_t' (y : ℤ) := ca_state t' y
    ca_rule_167 (C_t' (x - 1)) (C_t' x) (C_t' (x + 1))

/-- The sequence of bits forming the middle column of the CA pattern, $C_{t, 0}$. -/
def middle_column_bit (t : ℕ) : ℕ := ca_state t 0

/--
A267581: Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.
The term $a(n)$ is the decimal value of the binary number $C_{0, 0} C_{1, 0} \dots C_{n, 0}$,
where $C_{i, 0}$ is the state of the center cell at time $i$.
$$a(n) = \sum_{k=0}^n C_{k, 0} \cdot 2^{n-k}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (middle_column_bit k) * (2^ (n - k))

/-- The floor term in the conjectured recurrence relation for A267581.
This term, $\lfloor (1/2)^{(2^{n+1} \bmod n)} \rfloor$, simplifies to 1 if $(2^{n+1} \bmod n) = 0$
(i.e., $n \mid 2^{n+1}$), and 0 otherwise.
Since the recurrence is only stated for $n \ge 2$, the $n=0$ case is irrelevant to the conjecture. -/
def oeis_floor_term (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (2 ^ (n + 1)) % n = 0 then 1 else 0

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
def int_choose (n : ℕ) (k : ℤ) : ℕ :=
  if 0 ≤ k ∧ k ≤ n then Nat.choose n k.toNat else 0

def expected_state (t : ℕ) (x : ℤ) : ℕ :=
  if (x + t) % 2 = 0 then
    1 - (int_choose (t - 1) ((x + t - 2) / 2)) % 2
  else 1

lemma int_choose_pascal_mod2 (n : ℕ) (k : ℤ) :
  ((int_choose n k) % 2 + (int_choose n (k + 1)) % 2) % 2 = (int_choose (n + 1) (k + 1)) % 2 := by
  norm_num[int_choose]
  split_ifs
  · cases k with tauto
  · simp_all
  · norm_num[ (by valid:k=n)]
  · match k with|0|Nat.succ k=>omega
  · norm_num [ (by valid: k = -1)]
  · match n with|0 | S+1=>omega
  · match n with|0|n+1=>omega
  · rfl

lemma ca_rule_167_cases (cL cC cR : ℕ) (hL : cL ≤ 1) (hC : cC ≤ 1) (hR : cR ≤ 1) :
  ca_rule_167 cL cC cR =
  if cL = 0 ∧ cC = 0 ∧ cR = 0 then 1
  else if cL = 0 ∧ cC = 0 ∧ cR = 1 then 1
  else if cL = 0 ∧ cC = 1 ∧ cR = 0 then 1
  else if cL = 0 ∧ cC = 1 ∧ cR = 1 then 0
  else if cL = 1 ∧ cC = 0 ∧ cR = 0 then 0
  else if cL = 1 ∧ cC = 0 ∧ cR = 1 then 1
  else if cL = 1 ∧ cC = 1 ∧ cR = 0 then 0
  else 1 := by match cL with|_=>match cC with|0|1=>decide+revert

lemma ca_state_eq_expected (t : ℕ) (x : ℤ) :
  1 ≤ t → ca_state t x = expected_state t x := by
  induction t generalizing x with
  | zero =>
    intro h
    omega
  | succ t ih =>
    intro h
    rcases eq_or_lt_of_le (Nat.succ_le_succ_iff.mp h) with rfl | ht
    · norm_num[expected_state, true,ca_state]
      norm_num[parity_simps,ca_rule_167, add_eq_zero_iff_eq_neg.eq, sub_eq_zero,int_choose,<- (even_iff_two_dvd),add_sub_assoc]at*
      if R:x=1 ∨x=0 ∨x =-1 then{bound} else use .trans (by simp_all) (ite_eq_right_iff.2 fun and=>by rw [if_neg (and.elim (by valid))]).symm
    · simp_all! -contextual[Nat.succ_le]
      delta expected_state ca_rule_167 at*
      obtain ⟨s, _⟩| ⟨a, _⟩ := ( x+t).even_or_odd
      · norm_num[*, sub_add_eq_add_sub, add_right_comm x 1,←two_mul,int_choose,←add_assoc,←mul_sub_one]
        match i:ite ( _) _ _%2 with|0|1=>rfl | S+2=>omega
      norm_num[*, add_assoc, sub_add_eq_add_sub,int_choose,add_sub_assoc,Int.sub_ediv_of_dvd,←add_assoc]
      norm_num[*, add_assoc, add_left_comm x,add_sub]
      repeat' split
      · use (by valid:(1+ (2 *a+1)-2) / 2 = a).symm▸match t, a with|Nat.succ A,Nat.succ B=>A.choose_succ_succ B▸?_
        exact (mod_cast (by cases(A.choose B).mod_two_eq_zero_or_one with cases(A.choose B.succ).mod_two_eq_zero_or_one with push_cast[*,Nat.add_mod]))
      · match t with|1 | S+2=>omega
      · bound[ (by valid: a=t)]
      · match t with|1 | S+2=>omega
      · match t with|1 | S+2=>omega
      · match t with|1|h+2=>omega
      · bound[ (by valid: a=0)]
      · match t with|1|n+2=>omega
      · match t with|1|t+2=>omega
      · rfl
      · match t with|1 | S+2=>omega
      · match t with|1 | S+2=>omega

lemma expected_state_zero_eq (n : ℕ) (hn : 2 ≤ n) :
  expected_state n 0 = 1 - oeis_floor_term n := by
  norm_num[expected_state,oeis_floor_term]
  norm_num[int_choose,mt hn.trans_eq,←even_iff_two_dvd,←n.dvd_iff_mod_eq_zero,Nat.dvd_prime_pow]
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩:= n.even_or_odd
  · refine (if_pos (by use a)).trans (congr_arg ↑_ (.trans (by rw [ (by valid: (Int.toNat _) = a-1), if_pos (by valid)]) ?_))
    norm_num[ ←two_mul,a.add_sub_assoc (by valid: 1 ≤ a)]at *
    use two_mul a▸a.add_sub_assoc hn a▸(em _).elim (if_pos ·▸? _) (if_neg ·▸((Nat.prime_two.dvd_iff_one_le_factorization<|Nat.choose_ne_zero (by valid)).2 ?_).modEq_zero_nat)
    · rewrite[a.add_choose_eq]
      norm_num[ Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ']
      exact ( Finset.dvd_sum ((by valid:).elim fun and Y R M=>match and with|0=>by valid | S+1=>.mul_right ( (by valid: a=2^S)▸Nat.prime_two.dvd_choose_pow R.succ_ne_zero (by grind)) (_))).modEq_zero_nat.add_right (1)
    use Nat.prime_two.factorization_pos_of_dvd (Nat.choose_pos (by valid)).ne' ((Nat.prime_two.dvd_iff_one_le_factorization (Nat.choose_pos (by valid)).ne').2.comp (Nat.factorization_def _ (by decide)).ge.trans' ? _)
    convert (((padicValNat_choose _ _)).ge.trans' _)
    apply a +a
    · trivial
    · omega
    · exact (Nat.log_le_self _ _).trans_lt (by valid)
    use Finset.card_pos.2 ⟨(2).log a+1, Finset.mem_filter.2 ⟨ Finset.mem_Ico.2 (by_contra (absurd ((2).log_lt_self (ne_zero_of_lt hn)) ∘by valid)),Nat.add_sub_cancel _ _▸?_⟩⟩
    use(Nat.mod_eq_of_lt ((a.sub_le (1)).trans_lt ((2).lt_pow_succ_log_self (by decide) a))).symm▸(a.mod_eq_of_lt ((2).lt_pow_succ_log_self (by decide) _)).symm▸not_lt.1 (by valid ∘ fun and=>? _)
    exact ⟨(2).log a+1,by match(2).log_le_self a,(2).pow_log_le_self<|ne_zero_of_lt hn with|_, _=>omega⟩
  · rw[if_neg ↑(Nat.not_even_iff_odd.mpr ⟨a, rfl⟩),if_neg ↑(·.elim (by cases· with valid))]

lemma a_rec (n : ℕ) (hn : 1 ≤ n) :
  a n = 2 * a (n - 1) + middle_column_bit n := by
  delta a
  exact ( Finset.sum_range_succ _ _).trans (match n with | S+1 =>by push_cast+contextual[eq_self, ← Finset.mem_range_succ_iff,mul_left_comm, S.succ_sub, S.sub_self, mul_one, false,pow_succ', Finset.mul_sum, true,pow_zero])
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : 2 ≤ n) : a n = 2 * a (n - 1) + 1 - oeis_floor_term n := by
  -- EVOLVE-BLOCK-START
  have h1 : 1 ≤ n := by omega
  have h2 := a_rec n h1
  have h3 : middle_column_bit n = expected_state n 0 := by
    dsimp [middle_column_bit]
    rw [ca_state_eq_expected n 0 h1]
  have h4 := expected_state_zero_eq n hn
  have h5 : oeis_floor_term n ≤ 1 := by
    unfold oeis_floor_term
    split
    · exact Nat.zero_le 1
    · split
      · exact Nat.le_refl 1
      · exact Nat.zero_le 1
  omega
  -- EVOLVE-BLOCK-END
