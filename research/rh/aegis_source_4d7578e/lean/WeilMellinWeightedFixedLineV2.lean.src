import WeilFixedLineFubiniCoreV3
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
AEGIS Ω — first absolute Mellin moment on an arbitrary fixed vertical line v2.

The fixed-line proof in #490 uses not only vertical L1 integrability but also
the first absolute moment in height.  The existing Mellin inversion lane
already identifies each fixed Mellin line with the Fourier transform of a
compactly supported smooth logarithmic profile.  Such a profile is Schwartz,
its Fourier transform is Schwartz, and Mathlib's
`SchwartzMap.integrable_pow_mul` supplies the required polynomially weighted
L1 control.

This theorem is valid for every real line `σ`, in particular for the pair
`c` and `1-c` used by the paired-Hadamard fixed-line argument.

No zero sum, Fubini interchange, explicit-formula assembly, sign inequality,
or RH conclusion is asserted here.
-/

open Set Filter Topology Complex MeasureTheory
open scoped ContDiff FourierTransform

set_option autoImplicit false

noncomputable section

private theorem mellin_fixed_line_log_profile_contDiff_v2
    (f : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (MellinLogProfileV1 f.1) := by
  unfold MellinLogProfileV1
  have hneg : ContDiff ℝ ∞ (fun u : ℝ => -u) := by fun_prop
  exact f.2.1.comp (Real.contDiff_exp.comp hneg)

private theorem mellin_fixed_line_log_profile_hasCompactSupport_v2
    (f : WeilCompactSmoothGV1) :
    HasCompactSupport (MellinLogProfileV1 f.1) := by
  let K : Set ℝ := (fun x : ℝ => -Real.log x) '' tsupport f.1
  have hts : IsCompact (tsupport f.1) := by
    change IsCompact (closure (Function.support f.1))
    exact f.2.2.1
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (tsupport f.1) := by
    intro x hx
    have hxpos : 0 < x := f.2.2.2 hx
    exact (Real.continuousAt_log hxpos.ne').neg.continuousWithinAt
  have hK : IsCompact K := hts.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro u hu
  change f.1 (Real.exp (-u)) ≠ 0 at hu
  have hmem : Real.exp (-u) ∈ tsupport f.1 := subset_closure hu
  refine ⟨Real.exp (-u), hmem, ?_⟩
  simp

private theorem mellin_fixed_line_complex_weight_contDiff_v2 (σ : ℝ) :
    ContDiff ℝ ∞ (MellinComplexWeightV1 σ) := by
  unfold MellinComplexWeightV1 MellinWeightV1
  fun_prop

private theorem mellin_fixed_line_weighted_profile_contDiff_v2
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    ContDiff ℝ ∞ (MellinWeightedLogProfileV1 f.1 σ) := by
  unfold MellinWeightedLogProfileV1
  exact (mellin_fixed_line_complex_weight_contDiff_v2 σ).mul
    (mellin_fixed_line_log_profile_contDiff_v2 f)

private theorem mellin_fixed_line_weighted_profile_hasCompactSupport_v2
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    HasCompactSupport (MellinWeightedLogProfileV1 f.1 σ) := by
  have hh : HasCompactSupport (MellinLogProfileV1 f.1) :=
    mellin_fixed_line_log_profile_hasCompactSupport_v2 f
  apply hh.of_isClosed_subset (isClosed_tsupport _)
  change tsupport (fun u : ℝ =>
      MellinComplexWeightV1 σ u * MellinLogProfileV1 f.1 u) ⊆
    tsupport (MellinLogProfileV1 f.1)
  exact tsupport_mul_subset_right

private def MellinFixedLineSchwartzV2
    (f : WeilCompactSmoothGV1) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (mellin_fixed_line_weighted_profile_hasCompactSupport_v2 f σ).toSchwartzMap
    (mellin_fixed_line_weighted_profile_contDiff_v2 f σ)

private theorem mellin_fixed_line_eq_fourier_v2
    (f : WeilCompactSmoothGV1) (σ γ : ℝ) :
    mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I) =
      𝓕 (MellinFixedLineSchwartzV2 f σ) (γ / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hre : (((σ : ℂ) + (γ : ℂ) * Complex.I).re) = σ := by simp
  have him : (((σ : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
  rw [hre, him]
  have hprofile :
      (fun u : ℝ => Real.exp (-σ * u) • f.1 (Real.exp (-u))) =
        (MellinFixedLineSchwartzV2 f σ : ℝ → ℂ) := by
    funext u
    simp [MellinFixedLineSchwartzV2, MellinWeightedLogProfileV1,
      MellinComplexWeightV1, MellinWeightV1, MellinLogProfileV1,
      Complex.real_smul]
  rw [hprofile]
  rfl

/-- The first absolute height moment of the Mellin transform is integrable on
every real vertical line.  This is the A1 input used in the fixed-line Fubini
estimate of #490. -/
theorem weil_compact_smooth_mellin_vertical_abs_moment_one_v2
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    Integrable (fun γ : ℝ =>
      |γ| * ‖mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖) := by
  let P : SchwartzMap ℝ ℂ := MellinFixedLineSchwartzV2 f σ
  have hweighted :
      Integrable (fun ξ : ℝ => ‖ξ‖ ^ (1 : ℕ) * ‖(𝓕 P) ξ‖) :=
    (𝓕 P).integrable_pow_mul volume 1
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi0 : 2 * Real.pi ≠ 0 := ne_of_gt hpi
  have hscaled :=
    hweighted.comp_mul_right' (inv_ne_zero hpi0)
  have hconst := hscaled.const_mul (2 * Real.pi)
  have hpoint : ∀ γ : ℝ,
      |γ| * ‖mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ =
        2 * Real.pi *
          (‖γ * (2 * Real.pi)⁻¹‖ ^ (1 : ℕ) *
            ‖(𝓕 P) (γ * (2 * Real.pi)⁻¹)‖) := by
    intro γ
    rw [mellin_fixed_line_eq_fourier_v2]
    change |γ| * ‖(𝓕 P) (γ / (2 * Real.pi))‖ =
      2 * Real.pi *
        (‖γ * (2 * Real.pi)⁻¹‖ ^ (1 : ℕ) *
          ‖(𝓕 P) (γ * (2 * Real.pi)⁻¹)‖)
    rw [div_eq_mul_inv]
    simp only [pow_one, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos hpi]
    field_simp [hpi0]
  exact hconst.congr
    (Filter.Eventually.of_forall fun γ => (hpoint γ).symm)


/-- The second absolute height moment of the Mellin transform is integrable on
every real vertical line. This is the A2 input used by the strengthened FZ
majorant in WeilFixedLineFubiniCoreV3. -/
theorem weil_compact_smooth_mellin_vertical_abs_moment_two_v3
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    Integrable (fun γ : ℝ =>
      |γ| ^ 2 * ‖mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖) := by
  let P : SchwartzMap ℝ ℂ := MellinFixedLineSchwartzV2 f σ
  have hweighted :
      Integrable (fun ξ : ℝ => ‖ξ‖ ^ (2 : ℕ) * ‖(𝓕 P) ξ‖) :=
    (𝓕 P).integrable_pow_mul volume 2
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi0 : 2 * Real.pi ≠ 0 := ne_of_gt hpi
  have hscaled :=
    hweighted.comp_mul_right' (inv_ne_zero hpi0)
  have hconst := hscaled.const_mul ((2 * Real.pi) ^ 2)
  have hpoint : ∀ γ : ℝ,
      |γ| ^ 2 * ‖mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ =
        (2 * Real.pi) ^ 2 *
          (‖γ * (2 * Real.pi)⁻¹‖ ^ (2 : ℕ) *
            ‖(𝓕 P) (γ * (2 * Real.pi)⁻¹)‖) := by
    intro γ
    rw [mellin_fixed_line_eq_fourier_v2]
    change |γ| ^ 2 * ‖(𝓕 P) (γ / (2 * Real.pi))‖ =
      (2 * Real.pi) ^ 2 *
        (‖γ * (2 * Real.pi)⁻¹‖ ^ (2 : ℕ) *
          ‖(𝓕 P) (γ * (2 * Real.pi)⁻¹)‖)
    rw [div_eq_mul_inv]
    simp only [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpi]
    field_simp [hpi0]
  exact hconst.congr
    (Filter.Eventually.of_forall fun γ => (hpoint γ).symm)

/-- Concrete compact-smooth Mellin profiles satisfy the complete abstract
moment contract consumed by the FZ core: L1, first absolute moment, and second
absolute moment. -/
theorem weil_compact_smooth_mellin_has_vertical_norm_moments_two_v3
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    HasVerticalNormMomentsTwoV3
      (fun γ : ℝ => mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)) := by
  refine ⟨?_, weil_compact_smooth_mellin_vertical_abs_moment_one_v2 f σ,
    weil_compact_smooth_mellin_vertical_abs_moment_two_v3 f σ⟩
  exact weil_compact_smooth_mellin_vertical_integrable_all_v1 f σ

end

#print axioms weil_compact_smooth_mellin_vertical_abs_moment_one_v2
#print axioms weil_compact_smooth_mellin_vertical_abs_moment_two_v3
#print axioms weil_compact_smooth_mellin_has_vertical_norm_moments_two_v3
