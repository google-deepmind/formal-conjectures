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
module

public import Mathlib.RingTheory.Ideal.Height

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.List.Indexes
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Dimension formulas for polynomial rings

This file develops dimension results for prime quotients of polynomial rings over a field.
-/

@[expose] public section

open Ideal Polynomial MvPolynomial Nat RingHom List

namespace PolynomialCatenary

variable {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
  [Algebra R S]

/-- An injective integral extension preserves Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length]
  apply le_antisymm
  · refine WithBot.coe_le_coe.mpr (iSup_le fun l ↦ ?_)
    let mono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := fun _ _ h ↦
      Ideal.IsIntegral.comap_lt_comap h
    rw [← LTSeries.map_length l _ mono]
    exact le_iSup (fun p ↦ (p.length : ℕ∞)) (l.map _ mono)
  · refine WithBot.coe_le_coe.mpr (iSup_le fun l ↦ ?_)
    obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
    have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by
      simpa [PrimeSpectrum.ext_iff] using hP.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact le_iSup_of_le L (by simp [hlen])

/-- A prime polynomial ideal that contains a monic polynomial is maximal when its contraction is
maximal. -/
theorem Polynomial.isMaximal_of_monic_mem_of_comap_isMaximal
    {R : Type*} [CommRing R] (P : Ideal (Polynomial R)) [P.IsPrime]
    (g : Polynomial R) (hg : Polynomial.Monic g) (hgP : g ∈ P)
    (hP : (P.comap Polynomial.C).IsMaximal) :
    P.IsMaximal := by
  let f : R →+* (Polynomial R ⧸ P) := (Ideal.Quotient.mk P).comp Polynomial.C
  have hf : f.IsIntegral := hg.quotient_isIntegral hgP
  have hbot : (⊥ : Ideal (Polynomial R ⧸ P)).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf ⊥
    convert hP using 1
    ext x
    simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Ideal.mem_bot, f]
    exact Ideal.Quotient.eq_zero_iff_mem
  exact (Ideal.bot_quotient_isMaximal_iff P).mp hbot

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- A monic equation supplies the missing height-one step over the contraction of a prime
polynomial ideal. -/
theorem Polynomial.height_eq_comap_height_add_one_of_monic_mem
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal (Polynomial R)) [P.IsPrime]
    (g : Polynomial R) (hg : Polynomial.Monic g) (hgP : g ∈ P) :
    P.height = (P.comap Polynomial.C).height + 1 := by
  let p := P.comap Polynomial.C
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have hp' : p'.IsMaximal := by
    rw [p'_def, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal (Polynomial Rₚ) := P.map (algebraMap (Polynomial R) (Polynomial Rₚ))
  have disj : Disjoint (p.primeCompl.map Polynomial.C : Set (Polynomial R)) P := by
    simpa [p] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  let : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ P inferInstance disj
  let : P.LiesOver p := ⟨rfl⟩
  have hP'over : P'.LiesOver p' :=
    IsLocalization.liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  let : P'.LiesOver p' := hP'over
  have hgP' : g.map (algebraMap R Rₚ) ∈ P' := by
    change algebraMap (Polynomial R) (Polynomial Rₚ) g ∈ P'
    exact Ideal.mem_map_of_mem _ hgP
  have hP'max : P'.IsMaximal :=
    Polynomial.isMaximal_of_monic_mem_of_comap_isMaximal P'
      (g.map (algebraMap R Rₚ)) (hg.map _) hgP' (by
        have heq : P'.comap Polynomial.C = p' := by
          calc
            P'.comap Polynomial.C = P'.under Rₚ := by
              rw [Ideal.under_def, Polynomial.algebraMap_eq]
            _ = p' := hP'over.over.symm
        exact heq ▸ hp')
  let : P'.IsMaximal := hP'max
  have eq1 : p.height = p'.height := by
    rw [p'_def, IsLocalization.height_map_of_disjoint p.primeCompl]
    exact Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
  have eq2 : P.height = P'.height := by
    rw [IsLocalization.height_map_of_disjoint (Submonoid.map Polynomial.C p.primeCompl) _ disj]
  rw [show P.comap Polynomial.C = p from rfl, eq1, eq2]
  exact Polynomial.height_eq_height_add_one p' P'

namespace Triangular

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

variable {f v} in
lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The triangular change of variables used in Noether normalization. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- The triangular automorphism attached to a nonzero polynomial. -/
noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), r i * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- Distinct supported monomials acquire distinct degrees in the distinguished variable. -/
lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv,
    degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- The transformed polynomial has unit leading coefficient in the distinguished variable. -/
lemma T_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff_eq :
      (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
        (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff_eq
  simpa only [coeff_eq, algebraMap_eq] using
    (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end Triangular

variable {k : Type*} [Field k]

/-- For every prime ideal in a polynomial ring over a field, its height plus the dimension of its
quotient is the number of variables. -/
theorem MvPolynomial.height_add_ringKrullDim_quotient_eq_fin {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    P.height + ringKrullDim (MvPolynomial (Fin n) k ⧸ P) = n := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyRingEquiv k (Fin 0)
      have hmap : P.map e = ⊥ := Ideal.eq_bot_of_prime (P.map e)
      have hP : P = ⊥ := (Ideal.map_eq_bot_iff_of_injective e.injective).mp hmap
      subst P
      rw [Ideal.height_bot, WithBot.coe_zero, zero_add,
        ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
        ringKrullDim_eq_of_ringEquiv e]
      exact ringKrullDim_eq_zero_of_field k
  | succ n ih =>
      by_cases hP : P = ⊥
      · subst P
        rw [Ideal.height_bot, WithBot.coe_zero, zero_add,
          ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
          MvPolynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field k]
        simp
      · obtain ⟨f, hfP, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
        let e₁ := Triangular.T f
        let P₁ : Ideal (MvPolynomial (Fin (n + 1)) k) := P.map e₁
        have : P₁.IsPrime := Ideal.map_isPrime_of_equiv e₁
        let e₂ := MvPolynomial.finSuccEquiv k n
        let Q : Ideal (Polynomial (MvPolynomial (Fin n) k)) := P₁.map e₂
        have : Q.IsPrime := Ideal.map_isPrime_of_equiv e₂
        obtain hunit := Triangular.T_leadingCoeff_isUnit f hfne
        let g : Polynomial (MvPolynomial (Fin n) k) := hunit.unit⁻¹ • e₂ (e₁ f)
        have hgmonic : g.Monic :=
          Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hunit
        have hgf : g ∈ Q :=
          Submodule.smul_of_tower_mem Q hunit.unit⁻¹.val
            (Ideal.mem_map_of_mem e₂ (Ideal.mem_map_of_mem e₁ hfP))
        let q : Ideal (MvPolynomial (Fin n) k) := Q.comap Polynomial.C
        have : q.IsPrime := Ideal.IsPrime.comap Polynomial.C
        have hheightQ : Q.height = q.height + 1 :=
          Polynomial.height_eq_comap_height_add_one_of_monic_mem Q g hgmonic hgf
        have hind : q.height + ringKrullDim (MvPolynomial (Fin n) k ⧸ q) = n := ih q
        let : Algebra.IsIntegral (MvPolynomial (Fin n) k)
            (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) :=
          ⟨(Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hunit).quotient_isIntegral hgf⟩
        let : Algebra (MvPolynomial (Fin n) k ⧸ q)
            (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) :=
          Ideal.Quotient.algebraQuotientOfLEComap le_rfl
        let : Algebra.IsIntegral (MvPolynomial (Fin n) k ⧸ q)
            (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) :=
          ⟨(isIntegral_quotientMap_iff (f := Polynomial.C) (I := Q)).mpr
            Algebra.IsIntegral.isIntegral⟩
        have hdimQ : ringKrullDim (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) =
            ringKrullDim (MvPolynomial (Fin n) k ⧸ q) :=
          ringKrullDim_eq_of_isIntegral_of_injective
            (R := MvPolynomial (Fin n) k ⧸ q)
            (S := Polynomial (MvPolynomial (Fin n) k) ⧸ Q)
            (Ideal.quotientMap_injective (I := Q) (f := Polynomial.C))
        let quotientEquiv₁ :
            (MvPolynomial (Fin (n + 1)) k ⧸ P) ≃+*
              (MvPolynomial (Fin (n + 1)) k ⧸ P₁) :=
          Ideal.quotientEquiv P P₁ e₁.toRingEquiv rfl
        let quotientEquiv₂ :
            (MvPolynomial (Fin (n + 1)) k ⧸ P₁) ≃+*
              (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) :=
          Ideal.quotientEquiv P₁ Q e₂.toRingEquiv rfl
        have hheightP : P.height = Q.height := by
          calc
            P.height = P₁.height := (e₁.toRingEquiv.height_map P).symm
            _ = Q.height := (e₂.toRingEquiv.height_map P₁).symm
        have hdimP : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ P) =
            ringKrullDim (Polynomial (MvPolynomial (Fin n) k) ⧸ Q) := by
          calc
            _ = ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ P₁) :=
              ringKrullDim_eq_of_ringEquiv quotientEquiv₁
            _ = _ := ringKrullDim_eq_of_ringEquiv quotientEquiv₂
        rw [hheightP, hheightQ, hdimP, hdimQ, WithBot.coe_add, WithBot.coe_one]
        calc
          (q.height : WithBot ℕ∞) + 1 + ringKrullDim (MvPolynomial (Fin n) k ⧸ q) =
              ((q.height : WithBot ℕ∞) +
                ringKrullDim (MvPolynomial (Fin n) k ⧸ q)) + 1 := by ac_rfl
          _ = (n : WithBot ℕ∞) + 1 := congrArg (· + 1) hind
          _ = ((n + 1 : ℕ) : WithBot ℕ∞) := by norm_num

/-- If a prime ideal in a polynomial ring in `n` variables has height `p`, then its quotient has
Krull dimension `n - p`. -/
theorem MvPolynomial.ringKrullDim_quotient_eq_fin_sub_of_height_eq {n p : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] (hp : P.height = p) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ P) = n - p := by
  have h := MvPolynomial.height_add_ringKrullDim_quotient_eq_fin P
  rw [hp] at h
  obtain ⟨a, b, ha, hb, hab⟩ := WithBot.add_eq_coe.mp h
  have ha' : a = (p : ℕ∞) := WithBot.coe_injective ha
  subst a
  have hbtop : b ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hab
    exact ENat.top_ne_natCast n hab
  lift b to ℕ using hbtop with m
  have hpm : p + m = n := mod_cast hab
  rw [← hb, WithBot.coe_natCast]
  congr
  lia

end PolynomialCatenary
