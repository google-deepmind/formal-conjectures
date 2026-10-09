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

import RHKreinL105CheckerV1

/-!
# Tail, evenness and gluing for the `L = 21/20` certificate

* `tail_nonneg`: for `t ≥ X`, `Fcert t ≥ t⁴ (κ - B) ≥ 0` with
  `κ = midLower(X) - γ_u - log π_u - A₀ - 2/10⁹` (the prime cosine bounded by `1`) and
  `B = Σ_j |d_j| X^{j-4} + (2/50)·100²·Σ|c|·X⁻⁶`, checked by `decide`;
* `Fcert_even`;
* `glue`: two closed intervals sharing an end point.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinL105TailV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinL105TMV1
open AEGIS.RHKreinL105DataV1
open AEGIS.RHKreinL105CheckerV1
open AEGIS.RHKreinSymbolConstQV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaSharpTailV1

def kappa (P N : ℕ) (X : ℚ) : ℚ :=
  midLower P 0 N X - GAMMA_U - LOGPI_U - A0 - 2 / 10 ^ 9

def tailB (X : ℚ) : ℚ :=
  |dq 0| / X ^ 4 + |dq 1| / X ^ 3 + |dq 2| / X ^ 2 + |dq 3| / X + |dq 4| +
    2 / 50 * 100 ^ 2 * absSum cqList / X ^ 6

def tailCheck (P N : ℕ) (X : ℚ) : Bool := decide (0 < X) && decide (tailB X ≤ kappa P N X)

theorem symbol_tail (P N : ℕ) (a : ℚ) (t : ℝ) (ha : (0 : ℝ) ≤ a) (hat : (a : ℝ) ≤ t) :
    (kappa P N a : ℝ) ≤ symbol t := by
  have hst : (a : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
  have hsharp := digamma_quarter_sharp_lower t N
  unfold quarterPoint at hsharp
  have hmid := midSum_le P a t hst N 0
  simp only [zero_add] at hmid
  have hphi : ((a : ℝ) ^ 2 / 4) / (2 * ((N : ℝ) + 1 / 4) ^ 2 + (a : ℝ) ^ 2 / 4) ≤
      (t ^ 2 / 4) / (2 * ((N : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by
    have h1 : 0 < 2 * ((N : ℝ) + 1 / 4) ^ 2 + (a : ℝ) ^ 2 / 4 := by positivity
    have h2 : 0 < 2 * ((N : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by positivity
    rw [div_le_div_iff₀ h1 h2]
    have h3 : 0 ≤ 2 * ((N : ℝ) + 1 / 4) ^ 2 := by positivity
    nlinarith
  have hg := AEGIS.RHEulerGammaSharpBaseV1.gamma_lt_5773
  have hlp := logPi_upper
  have hamp := amp_close
  have hcos : Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2) ≤ A0 + 2 / 10 ^ 9 := by
    have h0 : 0 ≤ Real.sqrt 2 * Real.log 2 := by positivity
    have := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) h0
    have h2 := (abs_le.mp hamp).2
    linarith
  unfold symbol archSymbol kappa midLower GAMMA_U LOGPI_U
  push_cast
  simp only [Nat.sub_zero] at hmid ⊢
  push_cast at hmid
  linarith

theorem tail_nonneg (P N : ℕ) (X : ℚ) (h : tailCheck P N X = true) :
    ∀ t : ℝ, (X : ℝ) ≤ t → 0 ≤ Fcert t := by
  simp only [tailCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hX, hB⟩ := h
  intro t hXt
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have ht : 0 < t := lt_of_lt_of_le hX' hXt
  have hk := symbol_tail P N X t hX'.le hXt
  have hB' : (tailB X : ℝ) ≤ kappa P N X := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ tailB X := by
    unfold tailB; have := absSum_nonneg cqList; positivity
  have hk0 : (0 : ℝ) ≤ kappa P N X := hB0.trans hB'
  have hW : t ^ 4 ≤ (t ^ 2 + 1 / 4) ^ 2 := by nlinarith [sq_nonneg t]
  have hWk : t ^ 4 * (kappa P N X : ℝ) ≤ (t ^ 2 + 1 / 4) ^ 2 * symbol t :=
    mul_le_mul hW hk hk0 (by positivity)
  -- powers
  have hp : ∀ j : ℕ, j ≤ 4 → t ^ j ≤ t ^ 4 / (X : ℝ) ^ (4 - j) := by
    intro j hj
    rw [le_div_iff₀ (by positivity)]
    calc t ^ j * (X : ℝ) ^ (4 - j) ≤ t ^ j * t ^ (4 - j) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX'.le hXt _) (by positivity)
      _ = t ^ 4 := by rw [← pow_add]; congr 1; omega
  have hcs : ∀ (d : ℚ) (j k : ℕ) (y : ℝ), |y| ≤ 1 → j + k = 4 →
      -(|(d : ℝ)| * (t ^ 4 / (X : ℝ) ^ k)) ≤ (d : ℝ) * t ^ j * y := by
    intro d j k y hy hjk
    have hpj : t ^ j ≤ t ^ 4 / (X : ℝ) ^ k := by
      have := hp j (by omega)
      rwa [show 4 - j = k by omega] at this
    have h1 : |(d : ℝ) * t ^ j * y| ≤ |(d : ℝ)| * (t ^ 4 / (X : ℝ) ^ k) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ j)]
      calc |(d : ℝ)| * t ^ j * |y| ≤ |(d : ℝ)| * t ^ j * 1 :=
            mul_le_mul_of_nonneg_left hy (by positivity)
        _ ≤ |(d : ℝ)| * (t ^ 4 / (X : ℝ) ^ k) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hpj (abs_nonneg _)
    linarith [neg_abs_le ((d : ℝ) * t ^ j * y)]
  have d0 := hcs (dq 0) 0 4 _ (Real.abs_cos_le_one (t * L105)) rfl
  have d1 := hcs (dq 1) 1 3 _ (Real.abs_sin_le_one (t * L105)) rfl
  have d2 := hcs (dq 2) 2 2 _ (Real.abs_cos_le_one (t * L105)) rfl
  have d3 := hcs (dq 3) 3 1 _ (Real.abs_sin_le_one (t * L105)) rfl
  have d4 := hcs (dq 4) 4 0 _ (Real.abs_cos_le_one (t * L105)) rfl
  simp only [pow_zero, mul_one, pow_one, div_one] at d0 d1 d3 d4
  -- hats
  have hhat : -(2 / 50 * 100 ^ 2 * (absSum cqList : ℝ) / (X : ℝ) ^ 6 * t ^ 4) ≤ hatFun t := by
    have hS := abs_hatSumL_le cqList (107 / 100) t
    have hS0 : (0 : ℝ) ≤ absSum cqList := by exact_mod_cast absSum_nonneg cqList
    have hpos : 0 < t / 100 := by positivity
    have hsinc := sinc_sq_le_inv _ hpos
    have h1 : |hatFun t| ≤ 2 / 50 * (1 / (t / 100) ^ 2) * absSum cqList := by
      unfold hatFun
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / 50),
        abs_of_nonneg (sq_nonneg _)]
      apply mul_le_mul _ hS (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hsinc (by norm_num)
    have h2 : 2 / 50 * (1 / (t / 100) ^ 2) * (absSum cqList : ℝ) ≤
        2 / 50 * 100 ^ 2 * (absSum cqList : ℝ) / (X : ℝ) ^ 6 * t ^ 4 := by
      have h6 : (X : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ hX'.le hXt 6
      have hc : 0 ≤ 2 / 50 * 100 ^ 2 * (absSum cqList : ℝ) := by positivity
      have key : 2 / 50 * (1 / (t / 100) ^ 2) * (absSum cqList : ℝ) =
          (2 / 50 * 100 ^ 2 * (absSum cqList : ℝ) / (X : ℝ) ^ 6 * t ^ 4) * ((X : ℝ) ^ 6 / t ^ 6) := by
        field_simp <;> ring
      rw [key]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]; exact h6
    linarith [neg_abs_le (hatFun t)]
  have hBexp : (tailB X : ℝ) * t ^ 4 =
      |(dq 0 : ℝ)| * (t ^ 4 / (X : ℝ) ^ 4) + |(dq 1 : ℝ)| * (t ^ 4 / (X : ℝ) ^ 3) +
      |(dq 2 : ℝ)| * (t ^ 4 / (X : ℝ) ^ 2) + |(dq 3 : ℝ)| * (t ^ 4 / (X : ℝ)) +
      |(dq 4 : ℝ)| * t ^ 4 +
      2 / 50 * 100 ^ 2 * (absSum cqList : ℝ) / (X : ℝ) ^ 6 * t ^ 4 := by
    unfold tailB; push_cast; ring
  have hfin : (tailB X : ℝ) * t ^ 4 ≤ (kappa P N X : ℝ) * t ^ 4 :=
    mul_le_mul_of_nonneg_right hB' (by positivity)
  unfold Fcert deltaFun
  nlinarith

theorem Fcert_even (t : ℝ) : Fcert (-t) = Fcert t := by
  have hs : ∀ (l : List ℚ) (h : ℚ), hatSumL l h (-t) = hatSumL l h t := by
    intro l
    induction l with
    | nil => intro h; rfl
    | cons a l ih =>
      intro h; simp only [hatSumL, ih, neg_mul, Real.cos_neg]
  unfold Fcert hatFun deltaFun
  have hsym : symbol (-t) = symbol t := by
    unfold symbol archSymbol
    have hd : (Complex.digamma ((1 / 4 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I / 2)).re =
        (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
      apply le_antisymm
      · exact AEGIS.RHKreinDigammaMonotonicityV1.digamma_quarter_mono_of_sq_le (-t) t (by nlinarith)
      · exact AEGIS.RHKreinDigammaMonotonicityV1.digamma_quarter_mono_of_sq_le t (-t) (by nlinarith)
    rw [hd, show (-t) * Real.log 2 = -(t * Real.log 2) by ring, Real.cos_neg]
  rw [hsym, hs,
    show -t / 100 = -(t / 100) by ring, Real.sinc_neg]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg]
  ring

theorem glue {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ t, a ≤ t → t ≤ b → P t)
    (h2 : ∀ t, b ≤ t → t ≤ c → P t) : ∀ t, a ≤ t → t ≤ c → P t := by
  intro t hat htc
  by_cases htb : t ≤ b
  · exact h1 t hat htb
  · exact h2 t (le_of_lt (not_le.mp htb)) htc

end AEGIS.RHKreinL105TailV1

#print axioms AEGIS.RHKreinL105TailV1.tail_nonneg
#print axioms AEGIS.RHKreinL105TailV1.Fcert_even
