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
# Conjectures associated with A307865

A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.

A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.

*References:*
- [A307865](https://oeis.org/A307865)
-/

namespace OeisA307865

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Nat Finset ZMod

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

-- EVOLVE-BLOCK-START
lemma pow_add_nilpotent {R : Type*} [CommRing R] (y : R) (hy : y^2 = 0) (N : ℕ) :
    (1 + y)^N = 1 + N * y := by
  induction N with{norm_num [mul_assoc, mul_add, add_mul,←sq, add_assoc,pow_add, *] }

lemma odd_composite_cases (m : ℕ) (hm1 : m > 1) (hm_comp : ¬ Nat.Prime m) :
    (∃ p k : ℕ, Nat.Prime p ∧ k ≥ 2 ∧ m = p^k) ∨
    (∃ A B : ℕ, A > 1 ∧ B > 1 ∧ Nat.Coprime A B ∧ m = A * B) := by
  refine (by_contra.comp (m.exists_prime_and_dvd (by·omega) ).elim fun and a s=>absurd (m.ordProj_dvd and) ? _)
  use fun⟨A, B⟩=>s (.inr ⟨ _,A,by norm_num[m.factorization_eq_zero_iff,a,ne_zero_of_lt hm1,a.1.one_lt,Nat.succ_le,pos_iff_ne_zero],A.two_le_iff.mpr ? _,?_, B⟩)
  · use (by cases·▸B▸hm1),fun R=>s (.inl ⟨ _, _,a.1,(_: ℕ).two_le_iff.mpr (by repeat use (by norm_num[a, R▸·▸B]at *)),B▸(R▸mul_one _)⟩)
  · apply(a.1.coprime_iff_not_dvd.2 fun and' => (by norm_num[a, A.factorization_eq_zero_iff,a.1.ne_zero, right_ne_zero_of_mul (B▸hm1.ne_bot), and'] ∘congr_arg (·.factorization and)) B).pow_left

lemma no_such_base_case_1_h1 {n m p k : ℕ} (hm : m = 2 * n + 1)
    (hp : Nat.Prime p) (hk : k ≥ 2) (h_pk : m = p^k)
    (h_ny : (n : ZMod m) * (p^(k-1) : ZMod m) = 0) : False := by
  rw_mod_cast[CharP.cast_eq_zero_iff,] at h_ny
  cases h_pk with match k with | S+1 =>exact hp.not_dvd_one.comp (p.dvd_add_right<| ((Nat.mul_dvd_mul_iff_right (p.pow_pos hp.pos)).mp ↑(pow_succ' p S▸h_ny)).mul_left _).mp (hm▸dvd_pow_self p S.succ_ne_zero)

lemma no_such_base_case_1_h2 {m : ℕ} (hm_odd : Odd m) (hm1 : m > 1)
    (y n : ZMod m) (hy2 : y^2 = 0) (h_eq : 1 + n * y = -1) : False := by
  push_cast [←eq_sub_iff_add_eq'] at*
  match Fact.mk @hm1 with | S=>apply((((ZMod.isUnit_iff_coprime _ _).mpr) (hm_odd).coprime_two_left).pow 02).ne_zero (by linear_combination' hy2*n^2-h_eq*h_eq)

lemma no_such_base_case_1 {n m p k : ℕ} (hm : m = 2 * n + 1)
    (h_pseudoprime : IsAbsoluteEulerPseudoprime m)
    (hp : Nat.Prime p) (hk : k ≥ 2) (h_pk : m = p^k) : False := by
  have hm1 : m > 1 := h_pseudoprime.1
  have hm_odd : Odd m := by
    rw [hm]
    exact ⟨n, rfl⟩
  set y : ZMod m := p^(k-1)
  have hy2 : y^2 = 0 := by
    exact (pow_mul _ _ _).symm.trans (mod_cast(CharP.cast_eq_zero_iff _ _ _).2 (h_pk.dvd.trans (pow_dvd_pow p (by omega))))
  have h_x_inv : (1 + y) * (1 - y) = 1 := by
    linear_combination' hy2.symm
  have h_coprime : Nat.Coprime (1 + y).val m := by
    induction((hm1)) with apply ZMod.val_coe_unit_coprime (.mkOfMulEqOne _ _ (by valid) )
  have h_xn : (1 + y)^n = 1 ∨ (1 + y)^n = -1 := by
    delta IsAbsoluteEulerPseudoprime IsUnit at*
    induction @hm.symm with apply(n.mul_div_cancel_left ↑Nat.two_pos▸ZMod.natCast_zmod_val (1 +y)▸h_pseudoprime.2.2 _) ↑h_coprime
  have h_xn_val : (1 + y)^n = 1 + n * y := pow_add_nilpotent y hy2 n
  cases h_xn with
  | inl h1 =>
    have h_ny : (n : ZMod m) * y = 0 := by
      rwa[h_xn_val, add_eq_left] at h1
    exact no_such_base_case_1_h1 hm hp hk h_pk h_ny
  | inr h_minus1 =>
    have h_eq : 1 + (n : ZMod m) * y = -1 := by
      simp_all? only
    exact no_such_base_case_1_h2 hm_odd hm1 y n hy2 h_eq

lemma no_such_base_case_2_h1 {A B : ℕ} (hA : A > 1) (hAB_odd : Odd (A * B))
    (h1 : (-1 : ZMod A) = 1) : False := by
  match A with|02=>exact hAB_odd.not_two_dvd_nat ⟨ B, rfl⟩ | S+3=>rcases h1▸neg_add_cancel (1)

lemma no_such_base_case_2_h2 {A B : ℕ} (hB : B > 1) (hAB_odd : Odd (A * B))
    (h2 : (1 : ZMod B) = -1) : False := by
  use hB.ne' ((hAB_odd.of_dvd_nat (dvd_mul_left _ _)).coprime_two_right.eq_one_of_dvd ((CharP.cast_eq_zero_iff _ _ _).1 (by linear_combination' h2)))

lemma no_such_base_case_2 {n A B : ℕ} (hm : A * B = 2 * n + 1)
    (h_pseudoprime : IsAbsoluteEulerPseudoprime (A * B))
    (b : ZMod (A * B)) (hbn : b^n = -1)
    (hA : A > 1) (hB : B > 1) (hAB : Nat.Coprime A B) : False := by
  let f := ZMod.chineseRemainder hAB
  let bA : ZMod A := (f b).1
  have h_bA_n : bA^n = -1 := by
    linear_combination2(norm:=norm_num [bA])congr_arg (f · |>.fst) hbn
  let x : ZMod (A * B) := f.symm (bA, 1)
  have h_fx : f x = (bA, 1) := by
    apply@@f.apply_symm_apply
  have h_x_unit : IsUnit x := by
    norm_num[x,<-h_bA_n▸isUnit_pow_iff fun and=>by simp_all[ne_of_gt],Prod.isUnit_iff]
  have h_coprime : Nat.Coprime x.val (A * B) := by
    cases hA with cases hB with rwa[<-ZMod.isUnit_iff_coprime,x.natCast_zmod_val]
  have h_xn : x^n = 1 ∨ x^n = -1 := by
    norm_num[x,h_bA_n, true,←f.injective.eq_iff,Prod.ext_iff]
    delta IsAbsoluteEulerPseudoprime at *
    match NeZero.mk h_pseudoprime.1.ne_bot with | S=>use (by norm_num[x,Prod.ext_iff,←f.injective.eq_iff, *] ∘h_pseudoprime.2.2 _) h_coprime
  have h_fxn : f (x^n) = (bA^n, 1) := by
    norm_num[h_fx]
  have hAB_odd : Odd (A * B) := by
    rw [hm]
    exact ⟨n, rfl⟩
  cases h_xn with
  | inl h1 =>
    have h_eq : (bA^n, (1 : ZMod B)) = (1, 1) := by
      exact (h_fxn)▸ h1.symm▸@@f.map_one
    have h_A_eq : bA^n = 1 := by
      exact (congr_arg Prod.fst) h_eq
    have h_A_eq2 : (-1 : ZMod A) = 1 := by
      convert←h_A_eq
    exact no_such_base_case_2_h1 hA hAB_odd h_A_eq2
  | inr h_minus1 =>
    have h_eq : (bA^n, (1 : ZMod B)) = (-1, -1) := by
      convert←h_minus1▸f.map_neg (1)|>.trans (by rw [f.map_one])
    have h_B_eq : (1 : ZMod B) = -1 := by
      exact (congr_arg Prod.snd) h_eq
    exact no_such_base_case_2_h2 hB hAB_odd h_B_eq

lemma no_such_base {n m : ℕ} (hm : m = 2 * n + 1)
    (h_pseudoprime : IsAbsoluteEulerPseudoprime m)
    (b : ZMod m) (hbn : b^n = -1) : False := by
  have hm1 : m > 1 := h_pseudoprime.1
  have hm_odd : Odd m := by
    rw [hm]
    exact ⟨n, rfl⟩
  have hm_comp : ¬ Nat.Prime m := h_pseudoprime.2.1
  have cases := odd_composite_cases m hm1 hm_comp
  rcases cases with ⟨p, k, hp, hk, h_pk⟩ | ⟨A, B, hA, hB, hAB, h_AB⟩
  · exact no_such_base_case_1 hm h_pseudoprime hp hk h_pk
  · subst h_AB
    exact no_such_base_case_2 hm h_pseudoprime b hbn hA hB hAB

-- EVOLVE-BLOCK-END

@[category test, AMS 11]
lemma a_zero : a 0 = 0 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 0 := by rfl

@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/307865.wip.lean#L190"]
theorem target_theorem_0
  (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  -- EVOLVE-BLOCK-START
  have hm : 2 * n + 1 = 2 * n + 1 := rfl
  have : ∀ b_val, (b_val : ZMod (2 * n + 1)) ^ n ≠ -1 := by
    intro b_val h_eq
    exact no_such_base hm h (b_val : ZMod (2 * n + 1)) h_eq
  dsimp [a]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_false_of_mem
  intro b_val _
  exact this b_val
  -- EVOLVE-BLOCK-END

end OeisA307865
