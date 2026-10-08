import WeilMixedAlgebraV2
import WeilMellinInversionV1
import WeilAutocorrelationPoleAggregationV1
import Mathlib.Tactic

/-!
AEGIS Ω — finite-dilation two-moment filter V11.

This is a new producer used by the reverse restricted-Weil criterion.

For a compact-smooth positive-half-line packet f define

  A f(x) = f(x) - 3 f(2x) + 2 f(4x).

The operator stays in the exact repository carrier. Its Mellin transform is

  M(A f)(s)
    = (1 - 3*2^(-s) + 2*4^(-s)) M f(s),

so the two repository moments vanish identically because the scalar factor
vanishes at s=0 and s=1.

No zero, sign, or RH hypothesis is used.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFiniteDilationFilterV11

/-- Positive multiplicative dilation remains inside the exact compact-smooth
positive-half-line carrier. -/
def dilatePacketV11
    (f : WeilCompactSmoothGV1) (a : ℝ) (ha : 0 < a) :
    WeilCompactSmoothGV1 := by
  refine ⟨(fun x : ℝ => f.1 (x * a)), ?_, ?_, ?_⟩
  · exact f.2.1.comp (by fun_prop)
  · have h :=
      f.2.2.1.comp_homeomorph
        (Homeomorph.mulRight₀ a ha.ne')
    simpa [Function.comp_def] using h
  · intro x hx
    have hxa :
        x * a ∈ tsupport f.1 :=
      tsupport_comp_subset_preimage
        (f := fun y : ℝ => y * a) f.1 (by fun_prop) hx
    have hpos : 0 < x * a := f.2.2.2 hxa
    nlinarith

@[simp] theorem dilatePacketV11_apply
    (f : WeilCompactSmoothGV1) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    (dilatePacketV11 f a ha).1 x = f.1 (x * a) := rfl

/-- Scalar Mellin multiplier of the filter. -/
def FiniteDilationFactorV11 (s : ℂ) : ℂ :=
  1 - 3 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)

/-- Exact packet-valued finite-dilation filter. Existing mixed-algebra closure
is used only for carrier closure; the Mellin calculation below is independent. -/
def FiniteDilationFilterV11
    (f : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  AEGIS.WeilMixedAlgebraV2.combo
    1 (-3) 2
    f
    (dilatePacketV11 f 2 (by norm_num))
    (dilatePacketV11 f 4 (by norm_num))

@[simp] theorem finiteDilationFilter_apply_v11
    (f : WeilCompactSmoothGV1) (x : ℝ) :
    (FiniteDilationFilterV11 f).1 x =
      f.1 x - 3 * f.1 (x * 2) + 2 * f.1 (x * 4) := by
  simp [FiniteDilationFilterV11, AEGIS.WeilMixedAlgebraV2.combo]
  ring

/-- Exact Mellin multiplier identity for the finite-dilation filter. -/
theorem mellin_finiteDilationFilter_v11
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (FiniteDilationFilterV11 f).1 s =
      FiniteDilationFactorV11 s * mellin f.1 s := by
  let f2 := dilatePacketV11 f 2 (by norm_num)
  let f4 := dilatePacketV11 f 4 (by norm_num)

  have hf : MellinConvergent f.1 s :=
    weil_compact_smooth_mellin_convergent_all_v1 f s
  have hf2 : MellinConvergent f2.1 s :=
    weil_compact_smooth_mellin_convergent_all_v1 f2 s
  have hf4 : MellinConvergent f4.1 s :=
    weil_compact_smooth_mellin_convergent_all_v1 f4 s

  have h2 :
      mellin f2.1 s =
        (2 : ℂ) ^ (-s) * mellin f.1 s := by
    dsimp [f2, dilatePacketV11]
    simpa [smul_eq_mul] using
      (mellin_comp_mul_right f.1 s (show (0 : ℝ) < 2 by norm_num))

  have h4 :
      mellin f4.1 s =
        (4 : ℂ) ^ (-s) * mellin f.1 s := by
    dsimp [f4, dilatePacketV11]
    simpa [smul_eq_mul] using
      (mellin_comp_mul_right f.1 s (show (0 : ℝ) < 4 by norm_num))

  have hneg3 : MellinConvergent (fun x : ℝ => (-3 : ℂ) * f2.1 x) s := by
    simpa [smul_eq_mul] using hf2.const_smul (-3 : ℂ)
  have htwo : MellinConvergent (fun x : ℝ => (2 : ℂ) * f4.1 x) s := by
    simpa [smul_eq_mul] using hf4.const_smul (2 : ℂ)
  have hfirst :
      HasMellin
        (fun x : ℝ => f.1 x + (-3 : ℂ) * f2.1 x)
        s
        (mellin f.1 s + mellin (fun x : ℝ => (-3 : ℂ) * f2.1 x) s) :=
    hasMellin_add hf hneg3
  have hall :
      HasMellin
        (fun x : ℝ =>
          (f.1 x + (-3 : ℂ) * f2.1 x) + (2 : ℂ) * f4.1 x)
        s
        (mellin (fun x : ℝ => f.1 x + (-3 : ℂ) * f2.1 x) s +
          mellin (fun x : ℝ => (2 : ℂ) * f4.1 x) s) :=
    hasMellin_add hfirst.1 htwo

  have hlin := hall.2
  rw [mellin_const_smul, mellin_const_smul] at hlin

  change
    mellin (FiniteDilationFilterV11 f).1 s =
      FiniteDilationFactorV11 s * mellin f.1 s
  have hfun :
      (FiniteDilationFilterV11 f).1 =
        fun x : ℝ =>
          (f.1 x + (-3 : ℂ) * f2.1 x) + (2 : ℂ) * f4.1 x := by
    funext x
    simp [FiniteDilationFilterV11, f2, f4,
      AEGIS.WeilMixedAlgebraV2.combo]
    ring
  rw [hfun, hlin, h2, h4]
  unfold FiniteDilationFactorV11
  ring

@[simp] theorem finiteDilationFactor_zero_v11 :
    FiniteDilationFactorV11 0 = 0 := by
  simp [FiniteDilationFactorV11]

@[simp] theorem finiteDilationFactor_one_v11 :
    FiniteDilationFactorV11 1 = 0 := by
  simp [FiniteDilationFactorV11, Complex.cpow_neg_one]
  norm_num


/-- Algebraic factorization of the finite-dilation multiplier. -/
theorem finiteDilationFactor_factor_v11 (s : ℂ) :
    FiniteDilationFactorV11 s =
      (1 - (2 : ℂ) ^ (-s)) *
        (1 - (2 : ℂ) ^ (1 - s)) := by
  have h4 :
      (4 : ℂ) ^ (-s) =
        (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    calc
      (4 : ℂ) ^ (-s)
          = ((2 : ℂ) * (2 : ℂ)) ^ (-s) := by norm_num
      _ = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
          simpa using
            (Complex.mul_cpow_ofReal_nonneg
              (a := (2 : ℝ)) (b := (2 : ℝ))
              (by norm_num) (by norm_num) (-s))
  have h2 :
      (2 : ℂ) ^ (1 - s) =
        2 * (2 : ℂ) ^ (-s) := by
    calc
      (2 : ℂ) ^ (1 - s)
          = (2 : ℂ) ^ ((1 : ℂ) + (-s)) := by congr 1 <;> ring
      _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by
          rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = 2 * (2 : ℂ) ^ (-s) := by simp
  rw [FiniteDilationFactorV11, h4, h2]
  ring

/-- NEW LOAD-BEARING PRODUCER: the two-moment filter does not kill any
Mellin value in the strict critical strip. -/
theorem finiteDilationFactor_ne_zero_in_strip_v11
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    FiniteDilationFactorV11 s ≠ 0 := by
  rw [finiteDilationFactor_factor_v11]
  apply mul_ne_zero
  · intro h
    have heq : (2 : ℂ) ^ (-s) = 1 := by
      exact (sub_eq_zero.mp h).symm
    have hnorm :
        ‖(2 : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [heq, norm_one] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  · intro h
    have heq : (2 : ℂ) ^ (1 - s) = 1 := by
      exact (sub_eq_zero.mp h).symm
    have hnorm :
        1 < ‖(2 : ℂ) ^ (1 - s)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.one_lt_rpow (by norm_num)
      simp only [sub_re, one_re]
      linarith
    rw [heq, norm_one] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm

/-- Filtering preserves nonvanishing at every strict-strip Mellin point. -/
theorem finiteDilationFilter_mellin_ne_zero_in_strip_v11
    (f : WeilCompactSmoothGV1) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hf : mellin f.1 s ≠ 0) :
    mellin (FiniteDilationFilterV11 f).1 s ≠ 0 := by
  rw [mellin_finiteDilationFilter_v11]
  exact mul_ne_zero
    (finiteDilationFactor_ne_zero_in_strip_v11 h0 h1) hf

/-- The filtered packet has Mellin value zero at s=0. -/
theorem finiteDilationFilter_mellin_zero_v11
    (f : WeilCompactSmoothGV1) :
    mellin (FiniteDilationFilterV11 f).1 0 = 0 := by
  rw [mellin_finiteDilationFilter_v11, finiteDilationFactor_zero_v11,
    zero_mul]

/-- The filtered packet has Mellin value zero at s=1. -/
theorem finiteDilationFilter_mellin_one_v11
    (f : WeilCompactSmoothGV1) :
    mellin (FiniteDilationFilterV11 f).1 1 = 0 := by
  rw [mellin_finiteDilationFilter_v11, finiteDilationFactor_one_v11,
    zero_mul]

/-- NEW PRODUCER: the finite-dilation operator automatically discharges the
repository's two moment conditions for every seed packet. -/
theorem finiteDilationFilter_moments_v11
    (f : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 (FiniteDilationFilterV11 f) := by
  constructor
  · rw [← weil_mellin_zero_eq_moment0_v1 (FiniteDilationFilterV11 f)]
    exact finiteDilationFilter_mellin_zero_v11 f
  · rw [← weil_mellin_one_eq_moment1_v1 (FiniteDilationFilterV11 f)]
    exact finiteDilationFilter_mellin_one_v11 f

end AEGIS.WeilFiniteDilationFilterV11

#print axioms AEGIS.WeilFiniteDilationFilterV11.mellin_finiteDilationFilter_v11
#print axioms AEGIS.WeilFiniteDilationFilterV11.finiteDilationFilter_moments_v11
