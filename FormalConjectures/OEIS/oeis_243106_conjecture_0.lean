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




open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k

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
def GoodDigit (b d : ℕ) : Prop := d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

def IsGood (b : ℕ) (X : ℤ) : Prop :=
  ∃ (m : ℕ) (A : ℕ → ℤ), (∀ i, A i = -1 ∨ A i = 0 ∨ A i = 1) ∧
    (X = (∑ i ∈ Finset.range m, A i * (b : ℤ) ^ i) ∨
     X = (∑ i ∈ Finset.range m, A i * (b : ℤ) ^ i) - 1)

lemma div_mod_helper (b : ℕ) (hb : b ≥ 5) (N : ℕ) (S : ℤ) (d : ℤ) (hd : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1)
  (hN : (N : ℤ) = d + b * S) :
  ((N / b : ℤ) = S ∨ (N / b : ℤ) = S - 1) ∧ GoodDigit b (N % b) := by
  use(hN▸d.add_mul_ediv_left S (by(((omega)))))▸? _,Set.mem_setOf.mpr (@? _)
  · use (by_contra fun and=>absurd (@d.ediv_add_emod b) (absurd (@d.emod_nonneg b) ∘ fun and=>absurd (@d.emod_lt_of_pos b) ∘?_))
    exact (fun A B=>‹¬_› (by if a:d/ b=0 then norm_num[a]else use .inr (by nlinarith only[hb, B (by omega), and, A (by omega), (by omega:-2≤d∧d ≤ 1),sq_pos_iff.2 a])))
  obtain ⟨rfl⟩|rfl|rfl|rfl:=hd
  · exact (.inr (.inr (.inl ((Nat.mod_eq_of_lt (by valid)).subst (b.modEq_of_dvd ⟨S-1,by grind⟩).symm))))
  · exact (.inr (.inr (.inr (Nat.mod_eq_of_lt (by valid) |>.subst (b.modEq_of_dvd ⟨S-1,by grind⟩).symm))))
  · exact (.inl (by zify[*, zero_add,Int.mul_emod_right]))
  · norm_num[*,hb.trans_lt',←Int.ofNat_inj,Int.emod_eq_of_lt]

lemma isGood_step (b : ℕ) (hb : b ≥ 5) (N : ℕ) (hN : N > 0) (hGood : IsGood b N) :
  IsGood b (N / b) ∧ GoodDigit b (N % b) := by
  rcases hGood with ⟨m, A, hA, hX⟩
  cases m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty] at hX
    omega
  | succ m' =>
    have h_sum : (∑ i ∈ Finset.range (m' + 1), A i * (b : ℤ) ^ i) = A 0 + (b : ℤ) * ∑ i ∈ Finset.range m', A (i + 1) * (b : ℤ) ^ i := by
      push_cast only [add_comm, mul_left_comm (A _),mul_one, false,pow_succ',pow_zero, true, Finset.sum_range_succ', Finset.mul_sum]
    have hd_cases : ∃ d : ℤ, (d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1) ∧ (N : ℤ) = d + (b : ℤ) * ∑ i ∈ Finset.range m', A (i + 1) * (b : ℤ) ^ i := by
      refine if a:_ then⟨ _,.inr (hA 0), a⟩else ⟨A 0-1,by match(hA) 0 with | S=>omega⟩
    rcases hd_cases with ⟨d, hd_val, hd_eq⟩
    have h_helper := div_mod_helper b hb N (∑ i ∈ Finset.range m', A (i + 1) * (b : ℤ) ^ i) d hd_val hd_eq
    constructor
    · rcases h_helper.1 with h_div | h_div
      · use m', (fun i => A (i + 1))
        constructor
        · intro i
          exact hA (i + 1)
        · left
          exact h_div
      · use m', (fun i => A (i + 1))
        constructor
        · intro i
          exact hA (i + 1)
        · right
          exact h_div
    · exact h_helper.2

lemma digits_good (b : ℕ) (hb : b ≥ 5) (N : ℕ) (hGood : IsGood b N) :
  ∀ d ∈ Nat.digits b N, GoodDigit b d := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro d hd
    cases N with
    | zero =>
      rw [Nat.digits_zero] at hd
      contradiction
    | succ N' =>
      have hN : N' + 1 > 0 := Nat.zero_lt_succ N'
      have step := isGood_step b hb (N' + 1) hN hGood
      have h_digits : Nat.digits b (N' + 1) = ((N' + 1) % b) :: Nat.digits b ((N' + 1) / b) := by
        rwa[b.digits_def' (by omega)]
      rw [h_digits] at hd
      simp only [List.mem_cons] at hd
      cases hd with
      | inl h_eq =>
        rw [h_eq]
        exact step.2
      | inr h_in =>
        apply ih ((N' + 1) / b)
        · exact (Nat.div_lt_self hN (by omega))
        · exact step.1
        · exact h_in

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (b n : ℕ) (hb : b ≥ 5) :
    ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
  -- EVOLVE-BLOCK-START
  intro σ hσ x d hd
  have h_x_val : x = b * ∑ i ∈ Finset.range n, σ (i + 1) * (b : ℤ) ^ i := by
    exact ( Finset.sum_Ico_eq_sum_range _ _ _).trans (by push_cast[eq_self,add_comm, true,mul_left_comm (@σ _), Finset.mul_sum, false,pow_succ'])
  have h_x_abs : x.natAbs = b * (∑ i ∈ Finset.range n, σ (i + 1) * (b : ℤ) ^ i).natAbs := by
    apply h_x_val▸Int.natAbs_mul _ _
  have h_digits_x : ∀ d ∈ Nat.digits b x.natAbs, d = 0 ∨ d ∈ Nat.digits b (∑ i ∈ Finset.range n, σ (i + 1) * (b : ℤ) ^ i).natAbs := by
    refine (by assumption▸by cases(Int.natAbs _) with·norm_num [hb.trans_lt',b.digits_def'])
  have h_d_cases := h_digits_x d hd
  cases h_d_cases with
  | inl hd_zero =>
    rw [hd_zero]
    left
    rfl
  | inr hd_in =>
    have h_isGood : IsGood b (∑ i ∈ Finset.range n, σ (i + 1) * (b : ℤ) ^ i).natAbs := by
      norm_num(config := {singlePass :=1})[IsGood] at hσ⊢
      rcases abs_choice (∑ a ∈.range (n : ℕ),σ (a+1)*b^a)
      · use (n : ℕ), fun and=>ite (and<n) (σ (and + 1))<|-1,by grind,.inl (by push_cast+contextual[eq_self,← Finset.mem_range, *])
      · use (n : ℕ), (if.<n then-σ (by valid+1)else 0), (by if a: · <(n) then cases (hσ _) (by push_cast) a with((norm_num[ *]))else·omega),.inl (by (norm_num +contextual [ ← Finset.mem_range, false, *]))
    have h_good := digits_good b hb (∑ i ∈ Finset.range n, σ (i + 1) * (b : ℤ) ^ i).natAbs h_isGood
    exact h_good d hd_in
  -- EVOLVE-BLOCK-END
