import WeilMellinInversionV1
import Mathlib.Tactic

/-!
An exact two-moment annihilator on the existing Weil test-function domain.

The finite dilation filter `f(x) - 3 f(2x) + 2 f(4x)` preserves smoothness and
compact positive support. Its Mellin multiplier vanishes at 0 and 1 and is
nonzero throughout the open critical strip. Thus imposing the repository's
two moments does not force the Mellin transform to vanish at any prescribed
nontrivial zero. These are test-function construction results, not positivity.
-/

open Set Complex MeasureTheory
open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-- Positive dilation preserves the repository's exact test-function carrier. -/
def WeilPositiveDilationV1 (f : WeilCompactSmoothGV1) (a : ℝ) (ha : 0 < a) :
    WeilCompactSmoothGV1 := by
  refine ⟨fun x => f.1 (a * x), f.2.1.comp (by fun_prop), ?_, ?_⟩
  · let K : Set ℝ := (fun y : ℝ => y / a) '' tsupport f.1
    have hK : IsCompact K := f.2.2.1.isCompact.image (by fun_prop)
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    refine ⟨a * x, subset_closure hx, ?_⟩
    exact mul_div_cancel_left₀ x ha.ne'
  · have hpre := tsupport_comp_subset_preimage f.1
      (show Continuous (fun x : ℝ => a * x) by fun_prop)
    intro x hx
    have hax : 0 < a * x := f.2.2.2 (hpre hx)
    exact (mul_pos_iff_of_pos_left ha).mp hax

/-- The finite dilation filter annihilating the Mellin moments at 0 and 1. -/
def WeilMomentAnnihilatorV1 (f : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 := by
  let f2 := WeilPositiveDilationV1 f 2 (by norm_num)
  let f4 := WeilPositiveDilationV1 f 4 (by norm_num)
  refine ⟨fun x => f.1 x - 3 * f2.1 x + 2 * f4.1 x,
    (f.2.1.sub (contDiff_const.mul f2.2.1)).add (contDiff_const.mul f4.2.1),
    (f.2.2.1.sub f2.2.2.1.mul_left).add f4.2.2.1.mul_left, ?_⟩
  intro x hx
  rcases tsupport_add (fun x => f.1 x - 3 * f2.1 x)
      (fun x => 2 * f4.1 x) hx with hx | hx
  · rcases tsupport_sub f.1 (fun x => 3 * f2.1 x) hx with hx | hx
    · exact f.2.2.2 hx
    · exact f2.2.2.2 (tsupport_mul_subset_right hx)
  · exact f4.2.2.2 (tsupport_mul_subset_right hx)

/-- Public evaluation equation for the filter, independent of its subtype proof. -/
theorem weil_moment_annihilator_apply_v1 (f : WeilCompactSmoothGV1) (x : ℝ) :
    (WeilMomentAnnihilatorV1 f).1 x =
      f.1 x - 3 * f.1 (2 * x) + 2 * f.1 (4 * x) := rfl

/-- Factored Mellin multiplier of the finite dilation filter. -/
def WeilMomentAnnihilatorMultiplierV1 (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-s)) * (1 - 2 * (2 : ℂ) ^ (-s))

private theorem mellin_const_mul_dilation_v1 (f : ℝ → ℂ) (s c : ℂ)
    {a : ℝ} (ha : 0 < a) :
    mellin (fun x => c * f (a * x)) s = c * (a : ℂ) ^ (-s) * mellin f s := by
  have hc := mellin_const_smul (fun x => f (a * x)) s c
  simp only [smul_eq_mul] at hc
  rw [hc, mellin_comp_mul_left f s ha]
  simp only [smul_eq_mul]
  ring

/-- The exact Mellin identity, with convergence supplied by compact support. -/
theorem weil_moment_annihilator_mellin_v1 (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilMomentAnnihilatorV1 f).1 s =
      WeilMomentAnnihilatorMultiplierV1 s * mellin f.1 s := by
  have hf := weil_compact_smooth_mellin_convergent_all_v1 f s
  have hf2 := (MellinConvergent.comp_mul_left (show (0 : ℝ) < 2 by norm_num)).mpr hf
  have hf4 := (MellinConvergent.comp_mul_left (show (0 : ℝ) < 4 by norm_num)).mpr hf
  have h3 : MellinConvergent (fun x => (3 : ℂ) * f.1 (2 * x)) s := by
    simpa only [smul_eq_mul] using hf2.const_smul (3 : ℂ)
  have h2 : MellinConvergent (fun x => (2 : ℂ) * f.1 (4 * x)) s := by
    simpa only [smul_eq_mul] using hf4.const_smul (2 : ℂ)
  have hsub := hasMellin_sub hf h3
  have hadd := hasMellin_add hsub.1 h2
  change mellin (fun x => f.1 x - 3 * f.1 (2 * x) + 2 * f.1 (4 * x)) s = _
  rw [hadd.2, hsub.2,
    mellin_const_mul_dilation_v1 f.1 s 3 (by norm_num),
    mellin_const_mul_dilation_v1 f.1 s 2 (by norm_num)]
  have hfour : (4 : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    convert Complex.mul_cpow_ofReal_nonneg
      (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 2 by norm_num) (-s) using 1 <;>
      norm_num
  norm_num only [Complex.ofReal_ofNat]
  rw [hfour]
  unfold WeilMomentAnnihilatorMultiplierV1
  ring

/-- The filter has both exact zero moments used by the existing Weil criterion. -/
theorem weil_moment_annihilator_moments_v1 (f : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 (WeilMomentAnnihilatorV1 f) := by
  have h0 := weil_moment_annihilator_mellin_v1 f 0
  have h1 := weil_moment_annihilator_mellin_v1 f 1
  have hzero : mellin (WeilMomentAnnihilatorV1 f).1 0 = 0 := by
    simpa [WeilMomentAnnihilatorMultiplierV1] using h0
  have hone : mellin (WeilMomentAnnihilatorV1 f).1 1 = 0 := by
    norm_num [WeilMomentAnnihilatorMultiplierV1, Complex.cpow_neg_one] at h1 ⊢
    exact h1
  constructor
  · simpa [mellin, Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hzero
  · simpa [mellin, smul_eq_mul] using hone

/-- The filter loses no Mellin evaluation in the open critical strip. -/
theorem weil_moment_annihilator_multiplier_ne_zero_v1 {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    WeilMomentAnnihilatorMultiplierV1 s ≠ 0 := by
  let u : ℂ := (2 : ℂ) ^ (-s)
  have hnorm : ‖u‖ = (2 : ℝ) ^ (-s.re) := by
    simpa [u] using Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < 2 by norm_num) (-s)
  have hu_lt : ‖u‖ < 1 := by
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hu_gt : (1 / 2 : ℝ) < ‖u‖ := by
    rw [hnorm]
    have h := Real.rpow_lt_rpow_of_exponent_lt
      (show (1 : ℝ) < 2 by norm_num) (show (-1 : ℝ) < -s.re by linarith)
    norm_num [Real.rpow_neg_one] at h ⊢
    exact h
  apply mul_ne_zero
  · intro h
    have hu : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu, norm_one] at hu_lt
    exact (lt_irrefl _ hu_lt)
  · intro h
    have hu : 2 * u = 1 := (sub_eq_zero.mp h).symm
    have hh := congrArg norm hu
    simp only [norm_mul, Complex.norm_ofNat, norm_one] at hh
    linarith

/-- A nonzero Mellin evaluation at a strip point survives the two moment constraints. -/
theorem weil_moment_annihilator_mellin_ne_zero_v1 (f : WeilCompactSmoothGV1)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hf : mellin f.1 s ≠ 0) :
    mellin (WeilMomentAnnihilatorV1 f).1 s ≠ 0 := by
  rw [weil_moment_annihilator_mellin_v1]
  exact mul_ne_zero (weil_moment_annihilator_multiplier_ne_zero_v1 hs0 hs1) hf

#print axioms weil_moment_annihilator_apply_v1
#print axioms weil_moment_annihilator_mellin_v1
#print axioms weil_moment_annihilator_moments_v1
#print axioms weil_moment_annihilator_multiplier_ne_zero_v1
#print axioms weil_moment_annihilator_mellin_ne_zero_v1
