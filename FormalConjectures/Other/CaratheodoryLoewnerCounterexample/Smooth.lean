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

import FormalConjecturesUtil
import FormalConjectures.Other.CaratheodoryLoewnerCounterexample.Defs
import FormalConjecturesForMathlib.Analysis.SpecialFunctions.FlatRpowExp
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Smoothness of the announced Carathéodory–Loewner counterexamples

The proof is split between the punctured plane, where branch independence is the main issue, and
the origin, where the flat exponential dominates every derivative.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Filter Topology
open scoped ContDiff

namespace CaratheodoryLoewnerCounterexample

noncomputable section

/-- The trigonometric seed is smooth as a real-valued function of the complex variable. -/
@[category API, AMS 26]
theorem counterexampleSeed_contDiff : ContDiff ℝ ∞ counterexampleSeed := by
  unfold counterexampleSeed
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    simpa [Complex.imCLM_apply] using Complex.imCLM.contDiff
  fun_prop

@[fun_prop, category API, AMS 26]
private theorem sin_hasTemperateGrowth : Function.HasTemperateGrowth Real.sin := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_sin_le_one n x

@[fun_prop, category API, AMS 26]
private theorem cos_hasTemperateGrowth : Function.HasTemperateGrowth Real.cos := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_cos_le_one n x

@[category API, AMS 26]
private theorem counterexampleSeed_hasTemperateGrowth :
    Function.HasTemperateGrowth counterexampleSeed := by
  unfold counterexampleSeed
  have hre : Function.HasTemperateGrowth (fun z : ℂ ↦ z.re) := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.hasTemperateGrowth
  have him : Function.HasTemperateGrowth (fun z : ℂ ↦ z.im) := by
    simpa [Complex.imCLM_apply] using Complex.imCLM.hasTemperateGrowth
  simp only [div_eq_mul_inv]
  fun_prop

private def cpowFalling : ℂ → ℕ → ℂ
  | _, 0 => 1
  | c, n + 1 => c * cpowFalling (c - 1) n

@[category API, AMS 26]
private theorem iteratedDeriv_cpow_const (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun w : ℂ ↦ w ^ c) z = cpowFalling c n * z ^ (c - n) := by
  induction n generalizing c with
  | zero => simp [cpowFalling]
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun w : ℂ ↦ w ^ c) =ᶠ[𝓝 z] fun w ↦ c * w ^ (c - 1) := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        simpa using ((hasDerivAt_id w).cpow_const hw).deriv
      rw [hderiv.iteratedDeriv_eq n]
      have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c - 1)) z :=
        (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
      rw [iteratedDeriv_const_mul hsmooth c, ih (c - 1)]
      have hexp : c - 1 - (n : ℂ) = c - ((n + 1 : ℕ) : ℂ) := by
        norm_num [Nat.cast_add]
        ring
      change c * (cpowFalling (c - 1) n * z ^ (c - 1 - (n : ℂ))) =
        (c * cpowFalling (c - 1) n) * z ^ (c - ((n + 1 : ℕ) : ℂ))
      rw [mul_assoc, hexp]

@[category API, AMS 26]
private theorem norm_iteratedFDeriv_cpow_const (c : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (fun w : ℂ ↦ w ^ (c : ℂ)) z‖ =
      ‖cpowFalling (c : ℂ) n‖ * ‖z‖ ^ (c - n) := by
  have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c : ℂ)) z :=
    (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
  rw [← hsmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cpow_const (c : ℂ) n hz,
    norm_mul]
  congr 1
  convert Complex.norm_cpow_real z (c - n) using 1
  push_cast
  ring

@[category API, AMS 26]
private theorem cpow_pos_mul (r : ℝ) (hr : 0 < r) {z c : ℂ} (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ c = (r : ℂ) ^ c * z ^ c := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, add_mul, Complex.exp_add,
    Complex.ofReal_log hr.le]

@[category API, AMS 26]
private theorem div_cpow_eq (k : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (100 / z) ^ ((k : ℂ) / 2) =
      (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2)) := by
  rw [div_eq_mul_inv]
  change (((100 : ℝ) : ℂ) * z⁻¹) ^ ((k : ℂ) / 2) =
    ((100 : ℂ) ^ ((k : ℂ) / 2)) * z ^ (-((k : ℂ) / 2))
  rw [cpow_pos_mul 100 (by norm_num)
      (inv_ne_zero (Complex.slitPlane_ne_zero hz)),
    Complex.inv_cpow z _ (Complex.slitPlane_arg_ne_pi hz), Complex.cpow_neg]
  norm_num

private def negConjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

@[simp, category API, AMS 26]
private theorem negConjLIE_apply (z : ℂ) : negConjLIE z = -star z := by
  rfl

private def branchPhase (k : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  a * (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2))

@[category API, AMS 26]
private theorem norm_iteratedFDeriv_branchPhase (k n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (branchPhase k a) z‖ =
      ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) n‖ * ‖z‖ ^ (-(k : ℝ) / 2 - n) := by
  have hsmooth : ContDiffAt ℝ n (fun w : ℂ ↦ w ^ (-((k : ℂ) / 2))) z :=
    ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt).of_le
      (mod_cast le_top)
  have hc : -((k : ℂ) / 2) = ((-(k : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [show branchPhase k a = fun w ↦
      (a * (100 : ℂ) ^ ((k : ℂ) / 2)) • w ^ (-((k : ℂ) / 2)) by
        funext w; simp [branchPhase],
    iteratedFDeriv_const_smul_apply' hsmooth, norm_smul, hc,
    norm_iteratedFDeriv_cpow_const (-(k : ℝ) / 2) n hz]
  push_cast
  ring

@[category API, AMS 26]
private theorem norm_iteratedFDeriv_branchPhase_comp_conj (k n : ℕ) (a : ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (branchPhase k a ∘ Complex.conjLIE) z‖ =
      ‖iteratedFDeriv ℝ n (branchPhase k a) (star z)‖ := by
  simpa [Complex.conjLIE_apply] using
    Complex.conjLIE.norm_iteratedFDeriv_comp_right (branchPhase k a) z n

@[category API, AMS 26]
private theorem norm_iteratedFDeriv_branchPhase_comp_negConj (k n : ℕ) (a : ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (branchPhase k a ∘ negConjLIE) z‖ =
      ‖iteratedFDeriv ℝ n (branchPhase k a) (-star z)‖ := by
  simpa using negConjLIE.norm_iteratedFDeriv_comp_right (branchPhase k a) z n

@[category API, AMS 26]
private theorem branchOscillatory_iteratedFDeriv_polynomial_bound (k n : ℕ) (a : ℂ)
    (ha : ‖a‖ = 1) (e : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, e z ∈ Complex.slitPlane → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖ ≤
        C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨d, C, hC, hseed⟩ :=
    counterexampleSeed_hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
  let P := k + n
  let B := 1 + ‖(100 : ℂ) ^ ((k : ℂ) / 2)‖ *
    ∑ i ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) i‖
  refine ⟨P * (d + n), Nat.factorial n * C * (1 + B) ^ d * B ^ n,
    by positivity, ?_⟩
  intro z hz hz_one
  have hz0 : z ≠ 0 := fun h ↦ Complex.slitPlane_ne_zero hz (by simp [h])
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hB : 1 ≤ B := by
    simp only [B, le_add_iff_nonneg_right]
    positivity
  let R : ℝ := ‖z‖ ^ (-(P : ℝ))
  have hR : 1 ≤ R := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hz_one
      (neg_nonpos.mpr (Nat.cast_nonneg P))
  let Q := B * R
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hB hR
  have hphase (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (branchPhase k a ∘ e) z‖ ≤ Q := by
    rw [e.norm_iteratedFDeriv_comp_right]
    rw [norm_iteratedFDeriv_branchPhase k i a hz]
    rw [LinearIsometryEquiv.norm_map]
    have hcoeff : ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤ B := by
      rw [norm_mul, ha, one_mul]
      have hi_mem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
      have hsum : ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤
          ∑ j ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖cpowFalling (-((k : ℂ) / 2)) j‖)
          (fun _ _ ↦ norm_nonneg _) hi_mem
      dsimp only [B]
      nlinarith [mul_le_mul_of_nonneg_left hsum (norm_nonneg ((100 : ℂ) ^ ((k : ℂ) / 2)))]
    have hexp : ‖z‖ ^ (-(k : ℝ) / 2 - i) ≤ R := by
      apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
      dsimp only [R, P]
      have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      linarith
    dsimp only [Q]
    exact mul_le_mul hcoeff hexp (Real.rpow_nonneg (norm_nonneg z) _) (by positivity)
  let s := e ⁻¹' Complex.slitPlane
  have hs : IsOpen s := Complex.isOpen_slitPlane.preimage e.continuous
  have hzs : z ∈ s := hz
  have hinner : ContDiffOn ℝ ∞ (branchPhase k a ∘ e) s := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.comp x ?_ e.contDiff.contDiffAt
    unfold branchPhase
    exact (contDiffAt_const.mul
      ((analyticAt_id.cpow analyticAt_const hx).restrictScalars.contDiffAt))
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i counterexampleSeed Set.univ
          ((branchPhase k a ∘ e) z)‖ ≤ C * (1 + Q) ^ d := by
    rw [iteratedFDerivWithin_univ]
    refine (hseed i hi _).trans ?_
    gcongr
    simpa only [norm_iteratedFDeriv_zero] using hphase 0 (zero_le n)
  have hinner_bound (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (branchPhase k a ∘ e) s z‖ ≤ Q ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hs hzs]
    exact (hphase i hin).trans (le_self_pow₀ hQ (Nat.ne_of_gt hi))
  have hcomp := norm_iteratedFDerivWithin_comp_le
    counterexampleSeed_contDiff.contDiffOn hinner (mod_cast le_top)
    uniqueDiffOn_univ hs.uniqueDiffOn (fun _ _ ↦ Set.mem_univ _) hzs houter hinner_bound
  rw [iteratedFDerivWithin_of_isOpen n hs hzs] at hcomp
  have h_one_add : 1 + Q ≤ (1 + B) * R := by
    dsimp only [Q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hR)]
  have hRpow : R ^ (d + n) = ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  calc
    ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖
        ≤ Nat.factorial n * (C * (1 + Q) ^ d) * Q ^ n := hcomp
    _ ≤ Nat.factorial n * (C * ((1 + B) * R) ^ d) * (B * R) ^ n := by
      gcongr
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * (R ^ d * R ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * R ^ (d + n) := by
      rw [pow_add]
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) *
        ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by rw [hRpow]

private def oscillatoryFactor (k : ℕ) (z : ℂ) : ℝ :=
  counterexampleSeed (Complex.cpow (100 / star z) ((k : ℂ) / 2))

@[category API, AMS 26]
private theorem oscillatoryFactor_eq_plus (k : ℕ) {z : ℂ}
    (hz : star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k 1 ∘ Complex.conjLIE) z) := by
  simpa [oscillatoryFactor, Function.comp_apply, Complex.conjLIE_apply, branchPhase] using
    congrArg counterexampleSeed (div_cpow_eq k hz)

private def radialArgument (z : ℂ) : ℝ :=
  Complex.normSq z * Real.exp (8 * Complex.normSq z)

private def radialFlat (z : ℂ) : ℝ :=
  Real.flatRpowExp (1 / 8 : ℝ) 1 (radialArgument z)

@[category API, AMS 26]
private theorem normSq_contDiff : ContDiff ℝ ∞ Complex.normSq := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    simpa [Complex.imCLM_apply] using Complex.imCLM.contDiff
  simpa only [Complex.normSq_apply] using hre.mul hre |>.add (him.mul him)

@[category API, AMS 26]
private theorem radialArgument_contDiff : ContDiff ℝ ∞ radialArgument := by
  unfold radialArgument
  exact normSq_contDiff.mul <| Real.contDiff_exp.comp <| contDiff_const.mul normSq_contDiff

@[category API, AMS 26]
private theorem radialArgument_zero : radialArgument 0 = 0 := by
  simp [radialArgument]

@[category API, AMS 26]
private theorem radialFlat_contDiff : ContDiff ℝ ∞ radialFlat := by
  unfold radialFlat
  exact (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)).comp radialArgument_contDiff

@[category API, AMS 26]
private theorem radialFlat_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialFlat 0 = 0 := by
  unfold radialFlat
  exact ContDiff.iteratedFDeriv_comp_zero_of_outer
    (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)) radialArgument_contDiff
    radialArgument_zero (Real.flatRpowExp.iteratedFDeriv_zero (by norm_num) (by norm_num)) n

private def radialAmplitude (z : ℂ) : ℝ :=
  radialFlat z * (Complex.normSq z / (1 + Complex.normSq z))

@[category API, AMS 26]
private theorem radialAmplitude_contDiff : ContDiff ℝ ∞ radialAmplitude := by
  unfold radialAmplitude
  apply radialFlat_contDiff.mul
  exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
    ne_of_gt (by have := Complex.normSq_nonneg z; linarith)

@[category API, AMS 26]
private theorem radialAmplitude_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialAmplitude 0 = 0 := by
  unfold radialAmplitude
  apply ContDiff.iteratedFDeriv_mul_zero_of_left radialFlat_contDiff
  · exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
      ne_of_gt (by have := Complex.normSq_nonneg z; linarith)
  · exact radialFlat_iteratedFDeriv_zero

@[category API, AMS 26]
private theorem radialAmplitude_isLittleO_norm_pow (m n : ℕ) :
    iteratedFDeriv ℝ m radialAmplitude =o[𝓝 0] fun z : ℂ ↦ ‖z‖ ^ n :=
  ContDiff.isLittleO_norm_pow_of_iteratedFDeriv_zero radialAmplitude_contDiff
    radialAmplitude_iteratedFDeriv_zero m n

@[category API, AMS 26]
private theorem radialFlat_eq (z : ℂ) (hz : z ≠ 0) :
    radialFlat z =
      Real.exp (-‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hx : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  rw [radialFlat, radialArgument,
    Real.flatRpowExp.of_pos _ _ (mul_pos hx (Real.exp_pos _))]
  have hpow : Complex.normSq z ^ (-(1 / 8 : ℝ)) = ‖z‖ ^ (-(1 : ℝ) / 4) := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    ring
  have hexp : Real.exp (8 * Complex.normSq z) ^ (-(1 / 8 : ℝ)) =
      Real.exp (-‖z‖ ^ 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Complex.normSq_eq_norm_sq]
    congr 1
    ring
  rw [Real.mul_rpow hx.le (Real.exp_pos _).le, hpow, hexp]
  congr 1
  ring

@[category API, AMS 26]
private theorem counterexample_eq_radialAmplitude (k : ℕ) (z : ℂ) (hz : z ≠ 0) :
    counterexample k z = radialAmplitude z * oscillatoryFactor k z + 10 ^ 10 := by
  have hexp :
      Real.exp (-(Real.rpow ‖z‖ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2))) =
        Real.exp (-(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))) := by
    congr 1
    change -(‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) =
      -(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))
    ring
  rw [counterexample, radialAmplitude, oscillatoryFactor, radialFlat_eq z hz,
    Complex.normSq_eq_norm_sq]
  ring_nf
  all_goals rw [hexp]
  all_goals ring

@[category API, AMS 26]
private lemma cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    (z ^ ((k : ℂ) / 2)) ^ 2 = z ^ k := by
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast]
  congr 1
  push_cast
  ring

@[category API, AMS 26]
private lemma alt_cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) ^ 2 = z ^ k := by
  rw [mul_pow, cpow_half_nat_sq, ← pow_mul]
  conv_lhs => lhs; rw [show k * 2 = 2 * k by omega]
  rw [pow_mul, Complex.I_sq]
  rw [neg_pow z k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]

@[category API, AMS 26]
private lemma counterexampleSeed_eq_of_sq_eq_sq {z w : ℂ} (h : z ^ 2 = w ^ 2) :
    counterexampleSeed z = counterexampleSeed w := by
  rcases eq_or_eq_neg_of_sq_eq_sq z w h with h | h
  · rw [h]
  · rw [h, counterexampleSeed_neg]

/-- The seed identifies the principal half-integral power with the smooth alternate branch based
at `-z`. This pointwise identity is useful for differentiating at points on the branch cut. -/
@[category API, AMS 26]
theorem counterexampleSeed_cpow_eq_alt (k : ℕ) (z : ℂ) :
    counterexampleSeed (z ^ ((k : ℂ) / 2)) =
      counterexampleSeed ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) :=
  counterexampleSeed_eq_of_sq_eq_sq <|
    (cpow_half_nat_sq z k).trans (alt_cpow_half_nat_sq z k).symm

@[category API, AMS 26]
private theorem oscillatoryFactor_eq_minus (k : ℕ) {z : ℂ}
    (hz : -star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
  have hneg : -(100 / star z) = 100 / (-star z) := by ring
  calc
    oscillatoryFactor k z =
        counterexampleSeed ((Complex.I ^ k) * ((-(100 / star z)) ^ ((k : ℂ) / 2))) := by
      simpa [oscillatoryFactor] using counterexampleSeed_cpow_eq_alt k (100 / star z)
    _ = counterexampleSeed
        ((Complex.I ^ k) * ((100 / (-star z)) ^ ((k : ℂ) / 2))) := by rw [hneg]
    _ = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
      rw [div_cpow_eq k hz]
      simp only [Function.comp_apply, negConjLIE_apply, branchPhase]
      ring_nf

@[category API, AMS 26]
private theorem oscillatoryFactor_iteratedFDeriv_polynomial_bound (k n : ℕ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (oscillatoryFactor k) z‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨Np, Cp, hCp, hp⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n 1 (by simp) Complex.conjLIE
  obtain ⟨Nm, Cm, hCm, hm⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n (Complex.I ^ k)
      (by simp) negConjLIE
  refine ⟨Np + Nm, Cp + Cm, add_nonneg hCp hCm, ?_⟩
  intro z hz hz_one
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpowp : ‖z‖ ^ (-(Np : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  have hpowm : ‖z‖ ^ (-(Nm : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane (star_ne_zero.mpr hz) with hslit | hslit
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k 1 ∘ Complex.conjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage Complex.continuous_conj |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_plus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cp * ‖z‖ ^ (-(Np : ℝ)) := hp z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowp hCp).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCm)
            (Real.rpow_nonneg (norm_nonneg z) _)
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k (Complex.I ^ k) ∘ negConjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage negConjLIE.continuous |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_minus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cm * ‖z‖ ^ (-(Nm : ℝ)) := hm z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowm hCm).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCp)
            (Real.rpow_nonneg (norm_nonneg z) _)

@[category API, AMS 26]
private theorem counterexampleSeed_cpow_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : ℂ ↦ counterexampleSeed (w ^ ((k : ℂ) / 2))) z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hz | hz
  · exact counterexampleSeed_contDiff.contDiffAt.comp z
      ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt)
  · have hq : ContDiffAt ℝ ∞
        (fun w : ℂ ↦ (Complex.I ^ k) * ((-w) ^ ((k : ℂ) / 2))) z :=
      ((analyticAt_const.mul
        (analyticAt_id.neg.cpow analyticAt_const hz)).restrictScalars.contDiffAt)
    apply (counterexampleSeed_contDiff.contDiffAt.comp z hq).congr_of_eventuallyEq
    filter_upwards
    intro w
    exact counterexampleSeed_cpow_eq_alt k w

@[category API, AMS 26]
private theorem oscillatoryFactor_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (oscillatoryFactor k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    simpa [Complex.conjLIE_apply] using Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  simpa [oscillatoryFactor, Function.comp_def] using
    (counterexampleSeed_cpow_contDiffAt k (div_ne_zero (by norm_num) hstar_ne)).comp z hinv

@[category API, AMS 26]
private theorem radialAmplitude_mul_oscillatory_flatness (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 ∧
      ∀ m, iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
  let s : Set ℂ := {0}ᶜ
  have hs : IsOpen s := isClosed_singleton.isOpen_compl
  have hosc : ContDiffOn ℝ ∞ (oscillatoryFactor k) s := by
    intro z hz
    exact (oscillatoryFactor_contDiffAt k (by simpa [s] using hz)).contDiffWithinAt
  have hflat : ∀ m, iteratedFDeriv ℝ m
      (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
    intro m
    have hsum : (fun z : ℂ ↦ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
        fun z ↦ ‖z‖ := by
      apply Asymptotics.IsLittleO.sum
      intro i hi
      obtain ⟨N, C, hC, hpoly⟩ :=
        oscillatoryFactor_iteratedFDeriv_polynomial_bound k (m - i)
      have hoscO : (iteratedFDeriv ℝ (m - i) (oscillatoryFactor k)) =O[𝓝[≠] 0]
          fun z : ℂ ↦ ‖z‖ ^ (-(N : ℝ)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 1 :=
          Filter.Eventually.filter_mono inf_le_left (Metric.ball_mem_nhds 0 one_pos)
        filter_upwards [self_mem_nhdsWithin, hball] with z hz hball
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hz_one : ‖z‖ ≤ 1 := by
          rw [Metric.mem_ball, dist_zero_right] at hball
          exact hball.le
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
        exact hpoly z hz hz_one
      have hamp := (radialAmplitude_isLittleO_norm_pow i (N + 1)).mono
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
      have hprod : (fun z : ℂ ↦
          ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
            ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
          fun z ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ)) :=
        hamp.norm_left.mul_isBigO hoscO.norm_left
      have htarget : (fun z : ℂ ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ))) =ᶠ[𝓝[≠] 0]
          fun z ↦ ‖z‖ := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [← Real.rpow_natCast, ← Real.rpow_add hr]
        have hN : ((N + 1 : ℕ) : ℝ) + -(N : ℝ) = 1 := by
          push_cast
          ring
        rw [hN, Real.rpow_one]
      simpa only [mul_assoc] using
        (hprod.congr' EventuallyEq.rfl htarget).const_mul_left (m.choose i : ℝ)
    rw [Asymptotics.isLittleO_iff] at hsum ⊢
    intro c hc
    filter_upwards [hsum hc, self_mem_nhdsWithin] with z hbound hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    have hmul := norm_iteratedFDerivWithin_mul_le
      radialAmplitude_contDiff.contDiffOn hosc hs.uniqueDiffOn (show z ∈ s by simpa [s] using hz)
      (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
    rw [iteratedFDerivWithin_of_isOpen m hs (show z ∈ s by simpa [s] using hz)] at hmul
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs (show z ∈ s by simpa [s] using hz)] at hmul
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖ := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [Real.norm_of_nonneg hsum_nonneg] at hbound
    exact hmul.trans (by simpa using hbound)
  refine ⟨?_, hflat⟩
  apply ContDiff.at_zero_of_iteratedFDeriv_isLittleO
  · intro z hz
    exact radialAmplitude_contDiff.contDiffAt.mul (oscillatoryFactor_contDiffAt k hz)
  · simp [radialAmplitude, radialFlat, radialArgument]
  · exact hflat

@[category API, AMS 26]
private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
      (id : ℂ → ℂ) :=
  (radialAmplitude_mul_oscillatory_flatness k).2 m

@[category API, AMS 26]
private theorem radialAmplitude_mul_oscillatory_contDiffAt_zero (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 :=
  (radialAmplitude_mul_oscillatory_flatness k).1

@[category API, AMS 26]
private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 = 0 := by
  have hcontinuous := (radialAmplitude_mul_oscillatory_contDiffAt_zero k)
    |>.continuousAt_iteratedFDeriv (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
  have hcontinuous' : Tendsto
      (iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z))
      (𝓝[≠] 0) (𝓝 (iteratedFDeriv ℝ m
        (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0)) :=
    hcontinuous.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  have hzero := (radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO k m).trans_tendsto
    (tendsto_id.mono_left inf_le_left)
  exact tendsto_nhds_unique' (NormedField.nhdsNE_neBot (0 : ℂ)) hcontinuous' hzero

/-- Away from the origin the principal-power formula is smooth. For odd `k`, evenness of the seed
removes the sign jump of the chosen square-root branch. -/
@[category research solved, AMS 26 53]
theorem counterexample_contDiffAt_of_ne_zero (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (counterexample k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    simpa [Complex.conjLIE_apply] using Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  have hseed : ContDiffAt ℝ ∞
      (fun w : ℂ ↦ counterexampleSeed ((100 / star w) ^ ((k : ℂ) / 2))) z :=
    by
      simpa [Function.comp_def] using
        (counterexampleSeed_cpow_contDiffAt k (div_ne_zero (by norm_num) hstar_ne)).comp z hinv
  apply (radialAmplitude_contDiff.contDiffAt.mul hseed).add contDiffAt_const
    |>.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact counterexample_eq_radialAmplitude k w hw

@[category API, AMS 26 53]
private theorem counterexample_contDiffAt_zero_all (k : ℕ) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  have hconstant : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (10 : ℝ) ^ 10) 0 := contDiffAt_const
  apply (radialAmplitude_mul_oscillatory_contDiffAt_zero k).add hconstant
    |>.congr_of_eventuallyEq
  filter_upwards
  intro z
  by_cases hz : z = 0
  · subst z
    simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
  · exact counterexample_eq_radialAmplitude k z hz

/-- At the origin the nonconstant part of `counterexample k` is flat: exponential decay dominates
the algebraic growth of every derivative of the oscillatory factor. -/
@[category research solved, AMS 26 53]
theorem counterexample_contDiffAt_zero (k : ℕ) (hk : 0 < k) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_contDiffAt_zero_all (k + 1)

/-- The first Fréchet derivative of the counterexample vanishes at the origin. -/
@[category API, AMS 26 53]
theorem counterexample_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (counterexample k) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hfun : counterexample (Nat.succ k) = fun z ↦
        radialAmplitude z * oscillatoryFactor (Nat.succ k) z + (10 : ℝ) ^ 10 := by
      funext z
      by_cases hz : z = 0
      · subst z
        simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
      · exact counterexample_eq_radialAmplitude (Nat.succ k) z hz
    rw [hfun]
    simp only [fderiv_add_const]
    ext v
    have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (Nat.succ k) 1
    have happ := congrArg (fun L : ℂ [×1]→L[ℝ] ℝ ↦ L ![v]) hzero
    simpa only [iteratedFDeriv_one_apply, ContinuousMultilinearMap.zero_apply] using happ

@[category API, AMS 26 53]
private theorem counterexample_fderiv_fderiv_zero_all (k : ℕ) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  have hfun : counterexample k = fun z ↦
      radialAmplitude z * oscillatoryFactor k z + (10 : ℝ) ^ 10 := by
    funext z
    by_cases hz : z = 0
    · subst z
      simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
    · exact counterexample_eq_radialAmplitude k z hz
  rw [hfun]
  simp only [fderiv_add_const]
  ext v w
  have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero k 2
  have happ := congrArg (fun L : ℂ [×2]→L[ℝ] ℝ ↦ L ![v, w]) hzero
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.zero_apply] using happ

/-- The second Fréchet derivative of the counterexample vanishes at the origin. This is the
flatness consequence used in the index computation. -/
@[category API, AMS 26 53]
theorem counterexample_fderiv_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_fderiv_fderiv_zero_all (k + 1)

/-- Each positive member of the announced family is smooth on the whole complex plane, including
at the origin. The flat exponential factor is essential at the origin. -/
@[category research solved, AMS 26 53]
theorem counterexample_contDiff (k : ℕ) (hk : 0 < k) : ContDiff ℝ ∞ (counterexample k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · simpa [hz] using counterexample_contDiffAt_zero k hk
  · exact counterexample_contDiffAt_of_ne_zero k hz

end

end CaratheodoryLoewnerCounterexample
