import WeilCriterionCompactSmoothV1
import ZeroShellAnalyticSynthesisV1
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
AEGIS Ω — compact-smooth Mellin vertical cubic decay v1.

This lane works on the existing conservative compact-smooth positive-half-line
class `WeilCompactSmoothGV1`. It proves a uniform cubic vertical-strip bound
for the Mellin transform and then converts that bound to the existing canonical
height-shell interface `HasCubicShellMellinDecayV1`.

The proof is RH-independent. It uses the whole strip `0 ≤ re(s) ≤ 1`, the
existing canonical shell index `ceil |im(s)|`, Mathlib's Mellin/Fourier
identity, and third-order Fourier derivative control.

MELLIN_VERTICAL_CUBIC_DECAY_V1
AUTOCORRELATION_COMPACT_SMOOTH_BRIDGE_OPEN
ZERO_COUNTING_BOUND_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex MeasureTheory
open scoped ContDiff FourierTransform

noncomputable section

/-- Log-coordinate profile used by Mathlib's Mellin/Fourier identity. -/
def MellinLogProfileV1 (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  f (Real.exp (-u))

/-- Real exponential weight appearing at fixed vertical-strip real part. -/
def MellinWeightV1 (σ u : ℝ) : ℝ :=
  Real.exp (-σ * u)

/-- Complex-valued view of the real exponential weight. -/
def MellinComplexWeightV1 (σ u : ℝ) : ℂ :=
  MellinWeightV1 σ u • (1 : ℂ)

/-- Fourier-side profile whose transform equals the Mellin transform. -/
def MellinWeightedLogProfileV1 (f : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  MellinComplexWeightV1 σ u * MellinLogProfileV1 f u

/-- Uniform vertical cubic decay, stated without division so the zero-frequency
case remains total and explicit. -/
def HasUniformMellinVerticalCubicDecayV1 (f : ℝ → ℂ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ σ : ℝ, σ ∈ Set.Icc 0 1 → ∀ γ : ℝ,
      (1 + |γ|) ^ 3 *
          ‖mellin f ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ D

private theorem mellin_log_profile_contDiff_v1 (g : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (MellinLogProfileV1 g.1) := by
  unfold MellinLogProfileV1
  have hneg : ContDiff ℝ ∞ (fun u : ℝ => -u) := by fun_prop
  exact g.2.1.comp (Real.contDiff_exp.comp hneg)

private theorem mellin_log_profile_hasCompactSupport_v1
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (MellinLogProfileV1 g.1) := by
  let K : Set ℝ := (fun x : ℝ => -Real.log x) '' tsupport g.1
  have hts : IsCompact (tsupport g.1) := by
    change IsCompact (closure (Function.support g.1))
    exact g.2.2.1
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (tsupport g.1) := by
    intro x hx
    have hxpos : 0 < x := g.2.2.2 hx
    exact (Real.continuousAt_log hxpos.ne').neg.continuousWithinAt
  have hK : IsCompact K := hts.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro u hu
  change g.1 (Real.exp (-u)) ≠ 0 at hu
  have hmem : Real.exp (-u) ∈ tsupport g.1 := subset_closure hu
  refine ⟨Real.exp (-u), hmem, ?_⟩
  simp

private theorem mellin_weight_contDiff_v1 (σ : ℝ) :
    ContDiff ℝ ∞ (MellinWeightV1 σ) := by
  unfold MellinWeightV1
  fun_prop

private theorem mellin_complex_weight_contDiff_v1 (σ : ℝ) :
    ContDiff ℝ ∞ (MellinComplexWeightV1 σ) := by
  unfold MellinComplexWeightV1
  exact (mellin_weight_contDiff_v1 σ).smul_const (1 : ℂ)

private theorem mellin_weight_iteratedDeriv_v1 (σ : ℝ) (n : ℕ) :
    iteratedDeriv n (MellinWeightV1 σ) =
      fun u : ℝ => (-σ) ^ n * Real.exp (-σ * u) := by
  change iteratedDeriv n (fun u : ℝ => Real.exp ((-σ) * u)) =
    fun u : ℝ => (-σ) ^ n * Real.exp ((-σ) * u)
  exact iteratedDeriv_exp_const_mul n (-σ)

private theorem mellin_complex_weight_iteratedDeriv_v1
    (σ : ℝ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (MellinComplexWeightV1 σ) u =
      (((-σ) ^ n * Real.exp (-σ * u) : ℝ) : ℂ) := by
  have hwTop : ContDiffAt ℝ ∞ (MellinWeightV1 σ) u :=
    (mellin_weight_contDiff_v1 σ).contDiffAt
  have hw : ContDiffAt ℝ (n : ℕ∞ω) (MellinWeightV1 σ) u :=
    hwTop.of_le (by exact_mod_cast le_top)
  change iteratedDeriv n (fun y : ℝ => MellinWeightV1 σ y • (1 : ℂ)) u =
    (((-σ) ^ n * Real.exp (-σ * u) : ℝ) : ℂ)
  rw [iteratedDeriv_smul_const hw]
  rw [congrFun (mellin_weight_iteratedDeriv_v1 σ n) u]
  simp [Complex.real_smul]

private theorem mellin_weighted_log_profile_contDiff_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) :
    ContDiff ℝ ∞ (MellinWeightedLogProfileV1 g.1 σ) := by
  unfold MellinWeightedLogProfileV1
  exact (mellin_complex_weight_contDiff_v1 σ).mul (mellin_log_profile_contDiff_v1 g)

private theorem mellin_weighted_log_profile_hasCompactSupport_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) :
    HasCompactSupport (MellinWeightedLogProfileV1 g.1 σ) := by
  have hh : HasCompactSupport (MellinLogProfileV1 g.1) :=
    mellin_log_profile_hasCompactSupport_v1 g
  apply hh.of_isClosed_subset (isClosed_tsupport _)
  change tsupport (fun u : ℝ =>
      MellinComplexWeightV1 σ u * MellinLogProfileV1 g.1 u) ⊆
    tsupport (MellinLogProfileV1 g.1)
  exact tsupport_mul_subset_right

private theorem mellin_weighted_log_profile_tsupport_subset_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) :
    tsupport (MellinWeightedLogProfileV1 g.1 σ) ⊆
      tsupport (MellinLogProfileV1 g.1) := by
  change tsupport (fun u : ℝ =>
      MellinComplexWeightV1 σ u * MellinLogProfileV1 g.1 u) ⊆
    tsupport (MellinLogProfileV1 g.1)
  exact tsupport_mul_subset_right

private theorem mellin_iteratedDeriv_hasCompactSupport_v1
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  have hF : HasCompactSupport (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv n
  rw [iteratedDeriv_eq_equiv_comp]
  exact hF.comp_left (map_zero _)

private theorem mellin_weighted_log_profile_deriv_integrable_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (MellinWeightedLogProfileV1 g.1 σ)) := by
  let p := MellinWeightedLogProfileV1 g.1 σ
  have hpcont : ContDiff ℝ ∞ p := mellin_weighted_log_profile_contDiff_v1 g σ
  have hpcomp : HasCompactSupport p :=
    mellin_weighted_log_profile_hasCompactSupport_v1 g σ
  have hpderivcont : Continuous (iteratedDeriv n p) :=
    hpcont.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  exact hpderivcont.integrable_of_hasCompactSupport
    (mellin_iteratedDeriv_hasCompactSupport_v1 hpcomp n)

private theorem mellin_log_profile_deriv_bound_v1
    (g : WeilCompactSmoothGV1) (i : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖iteratedDeriv i (MellinLogProfileV1 g.1) u‖ ≤ C := by
  let h := MellinLogProfileV1 g.1
  have hhcont : ContDiff ℝ ∞ h := mellin_log_profile_contDiff_v1 g
  have hhcomp : HasCompactSupport h := mellin_log_profile_hasCompactSupport_v1 g
  have hc : Continuous (iteratedDeriv i h) :=
    hhcont.continuous_iteratedDeriv i (by exact_mod_cast le_top)
  exact hc.bounded_above_of_compact_support
    (mellin_iteratedDeriv_hasCompactSupport_v1 hhcomp i)

/-- The weighted log profiles have a single L1 bound for derivatives of order
at most three, uniformly for `σ ∈ [0,1]`. -/
private theorem mellin_weighted_log_profile_uniform_l1_v1
    (g : WeilCompactSmoothGV1) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ σ : ℝ, σ ∈ Set.Icc 0 1 → ∀ n : ℕ, n ≤ 3 →
        (∫ u : ℝ,
          ‖iteratedDeriv n (MellinWeightedLogProfileV1 g.1 σ) u‖) ≤ L := by
  let h := MellinLogProfileV1 g.1
  have hhcont : ContDiff ℝ ∞ h := mellin_log_profile_contDiff_v1 g
  have hhcomp : HasCompactSupport h := mellin_log_profile_hasCompactSupport_v1 g
  have htscomp : IsCompact (tsupport h) := by
    change IsCompact (closure (Function.support h))
    exact hhcomp
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp htscomp.isBounded
  let R : ℝ := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have htsR : tsupport h ⊆ Metric.closedBall (0 : ℝ) R := by
    exact hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))

  obtain ⟨C0, hC0⟩ := mellin_log_profile_deriv_bound_v1 g 0
  obtain ⟨C1, hC1⟩ := mellin_log_profile_deriv_bound_v1 g 1
  obtain ⟨C2, hC2⟩ := mellin_log_profile_deriv_bound_v1 g 2
  obtain ⟨C3, hC3⟩ := mellin_log_profile_deriv_bound_v1 g 3
  let C : ℝ := max 0 (max C0 (max C1 (max C2 C3)))
  have hC : 0 ≤ C := le_max_left _ _
  have hC0' : C0 ≤ C :=
    (le_max_left C0 (max C1 (max C2 C3))).trans (le_max_right 0 _)
  have hC1' : C1 ≤ C :=
    (le_max_left C1 (max C2 C3)).trans
      ((le_max_right C0 _).trans (le_max_right 0 _))
  have hC2' : C2 ≤ C :=
    (le_max_left C2 C3).trans
      ((le_max_right C1 _).trans ((le_max_right C0 _).trans (le_max_right 0 _)))
  have hC3' : C3 ≤ C :=
    (le_max_right C2 C3).trans
      ((le_max_right C1 _).trans ((le_max_right C0 _).trans (le_max_right 0 _)))
  have hCderiv : ∀ i : ℕ, i ≤ 3 → ∀ u : ℝ,
      ‖iteratedDeriv i h u‖ ≤ C := by
    intro i hi u
    interval_cases i
    · exact (hC0 u).trans hC0'
    · exact (hC1 u).trans hC1'
    · exact (hC2 u).trans hC2'
    · exact (hC3 u).trans hC3'

  let M : ℝ := 8 * Real.exp R * C
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let K : Set ℝ := Metric.closedBall (0 : ℝ) R
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKfinite : volume K ≠ ⊤ := ne_of_lt measure_closedBall_lt_top
  let L : ℝ := ∫ _u : ℝ in K, M
  have hL : 0 ≤ L := by
    dsimp [L]
    exact setIntegral_nonneg hKmeas (fun _ _ => hM)

  refine ⟨L, hL, ?_⟩
  intro σ hσ n hn
  let p := MellinWeightedLogProfileV1 g.1 σ

  have hpcont : ContDiff ℝ ∞ p := mellin_weighted_log_profile_contDiff_v1 g σ
  have hp_ts : tsupport p ⊆ tsupport h :=
    mellin_weighted_log_profile_tsupport_subset_v1 g σ
  have hpint : Integrable (iteratedDeriv n p) :=
    mellin_weighted_log_profile_deriv_integrable_v1 g σ n

  have hsigma_abs : |σ| ≤ 1 := by
    rw [abs_of_nonneg hσ.1]
    exact hσ.2

  have hpoint : ∀ u ∈ K, ‖iteratedDeriv n p u‖ ≤ M := by
    intro u hu
    have huabs : |u| ≤ R := by
      simpa [K, Metric.mem_closedBall, Real.dist_eq] using hu
    have hexparg : -σ * u ≤ R := by
      calc
        -σ * u ≤ |σ * u| := by
          simpa [abs_mul] using le_abs_self (-σ * u)
        _ = |σ| * |u| := abs_mul σ u
        _ ≤ 1 * R := by gcongr
        _ = R := one_mul R
    have hexp : Real.exp (-σ * u) ≤ Real.exp R :=
      Real.exp_le_exp.mpr hexparg

    have hweight : ∀ i : ℕ,
        ‖iteratedDeriv i (MellinComplexWeightV1 σ) u‖ ≤ Real.exp R := by
      intro i
      rw [mellin_complex_weight_iteratedDeriv_v1]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]
      calc
        |(-σ)| ^ i * Real.exp (-σ * u)
            ≤ 1 ^ i * Real.exp R := by
              gcongr
              · simpa using hsigma_abs
        _ = Real.exp R := by simp

    change ‖iteratedDeriv n
      (fun x : ℝ => MellinComplexWeightV1 σ x * h x) u‖ ≤ M
    have hw_n : ContDiffAt ℝ (n : ℕ∞ω) (MellinComplexWeightV1 σ) u :=
      (mellin_complex_weight_contDiff_v1 σ).contDiffAt.of_le
        (by exact_mod_cast le_top)
    have hh_n : ContDiffAt ℝ (n : ℕ∞ω) h u :=
      hhcont.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_fun_mul hw_n hh_n]
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (MellinComplexWeightV1 σ) u *
              iteratedDeriv (n - i) h u‖
          ≤ ∑ i ∈ Finset.range (n + 1),
              ‖(n.choose i : ℂ) *
                iteratedDeriv i (MellinComplexWeightV1 σ) u *
                  iteratedDeriv (n - i) h u‖ := norm_sum_le ..
      _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * Real.exp R * C := by
        apply Finset.sum_le_sum
        intro i hi
        have hni : n - i ≤ 3 := (Nat.sub_le n i).trans hn
        simp only [norm_mul, Complex.norm_natCast, Real.norm_natCast]
        gcongr
        · exact hweight i
        · exact hCderiv (n - i) hni u
      _ = (2 : ℝ) ^ n * Real.exp R * C := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
      _ ≤ 8 * Real.exp R * C := by
        have hpow : (2 : ℝ) ^ n ≤ 8 := by
          interval_cases n <;> norm_num
        gcongr
      _ = M := by rfl

  have hsupport :
      Function.support (fun u : ℝ => ‖iteratedDeriv n p u‖) ⊆ K := by
    intro u hu
    have hder_ne : iteratedDeriv n p u ≠ 0 := by
      simpa using hu
    have hF_ne : iteratedFDeriv ℝ n p u ≠ 0 := by
      intro hz
      apply hder_ne
      rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, hz]
      simp
    have huts_p : u ∈ tsupport p :=
      support_iteratedFDeriv_subset n hF_ne
    exact htsR (hp_ts huts_p)

  have hzero : ∀ u : ℝ, u ∉ K → ‖iteratedDeriv n p u‖ = 0 := by
    intro u hu
    by_contra hne
    exact hu (hsupport hne)

  have hinter_eq :
      (∫ u : ℝ, ‖iteratedDeriv n p u‖) =
        ∫ u : ℝ in K, ‖iteratedDeriv n p u‖ := by
    rw [← integral_indicator hKmeas]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ K
    · simp [hu]
    · simp [hu, hzero u hu]

  rw [hinter_eq]
  dsimp [L]
  exact setIntegral_mono_on hpint.norm.integrableOn
    (integrableOn_const hKfinite) hKmeas hpoint

/-- Smooth compactly supported positive-half-line functions have uniform cubic
Mellin decay throughout the closed critical strip. -/
theorem weil_compact_smooth_mellin_vertical_cubic_decay_v1
    (g : WeilCompactSmoothGV1) :
    HasUniformMellinVerticalCubicDecayV1 g.1 := by
  obtain ⟨L, hL, hLbound⟩ := mellin_weighted_log_profile_uniform_l1_v1 g
  refine ⟨8 * L, by positivity, ?_⟩
  intro σ hσ γ
  let p := MellinWeightedLogProfileV1 g.1 σ
  let ξ : ℝ := γ / (2 * Real.pi)
  have hpcont : ContDiff ℝ ∞ p := mellin_weighted_log_profile_contDiff_v1 g σ
  have hpcontFourier : ContDiff ℝ (3 : ℕ∞) p := by
    exact hpcont.of_le (mod_cast le_top)
  have hpint : ∀ n : ℕ, Integrable (iteratedDeriv n p) :=
    fun n => mellin_weighted_log_profile_deriv_integrable_v1 g σ n
  have hL0 := hLbound σ hσ 0 (by omega)
  have hL3 := hLbound σ hσ 3 (by omega)

  have hmellin :
      mellin g.1 ((σ : ℂ) + (γ : ℂ) * Complex.I) = 𝓕 p ξ := by
    rw [mellin_eq_fourier]
    have hre : (((σ : ℂ) + (γ : ℂ) * Complex.I).re) = σ := by simp
    have him : (((σ : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
    rw [hre, him]
    change 𝓕 (fun u : ℝ => Real.exp (-σ * u) • g.1 (Real.exp (-u)))
        (γ / (2 * Real.pi)) =
      𝓕 (MellinWeightedLogProfileV1 g.1 σ) (γ / (2 * Real.pi))
    have hprofile :
        (fun u : ℝ => Real.exp (-σ * u) • g.1 (Real.exp (-u))) =
          MellinWeightedLogProfileV1 g.1 σ := by
      funext u
      simp [MellinWeightedLogProfileV1, MellinComplexWeightV1,
        MellinWeightV1, MellinLogProfileV1, Complex.real_smul]
    rw [hprofile]

  have hfourier0 : ‖𝓕 p ξ‖ ≤ L := by
    calc
      ‖𝓕 p ξ‖ ≤ ∫ u : ℝ, ‖p u‖ := by
        rw [Real.fourier_eq]
        calc
          ‖∫ u : ℝ, 𝐞 (-inner ℝ u ξ) • p u‖
              ≤ ∫ u : ℝ, ‖𝐞 (-inner ℝ u ξ) • p u‖ :=
                norm_integral_le_integral_norm _
          _ = ∫ u : ℝ, ‖p u‖ := by
            apply integral_congr_ae
            filter_upwards with u
            simp [Circle.norm_smul]
      _ ≤ L := by
        simpa using hL0

  have hfourier3 :
      ‖𝓕 (iteratedDeriv 3 p) ξ‖ ≤ L := by
    calc
      ‖𝓕 (iteratedDeriv 3 p) ξ‖
          ≤ ∫ u : ℝ, ‖iteratedDeriv 3 p u‖ := by
        rw [Real.fourier_eq]
        calc
          ‖∫ u : ℝ, 𝐞 (-inner ℝ u ξ) • iteratedDeriv 3 p u‖
              ≤ ∫ u : ℝ, ‖𝐞 (-inner ℝ u ξ) • iteratedDeriv 3 p u‖ :=
                norm_integral_le_integral_norm _
          _ = ∫ u : ℝ, ‖iteratedDeriv 3 p u‖ := by
            apply integral_congr_ae
            filter_upwards with u
            simp [Circle.norm_smul]
      _ ≤ L := hL3

  have hderiv_fourier :=
    congrFun
      (Real.fourier_iteratedDeriv
        (N := (3 : ℕ∞)) (n := 3) hpcontFourier
        (fun n _ => hpint n) (by norm_num)) ξ

  have hfreq :
      |γ| ^ 3 * ‖𝓕 p ξ‖ ≤ L := by
    have hnormfactor :
        ‖((2 * Real.pi * Complex.I * ξ) ^ 3 : ℂ)‖ = |γ| ^ 3 := by
      simp [ξ, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_ne_zero]
    have htmp :
        ‖((2 * Real.pi * Complex.I * ξ) ^ 3 : ℂ) • 𝓕 p ξ‖ ≤ L := by
      rw [← hderiv_fourier]
      exact hfourier3
    simpa [norm_smul, hnormfactor] using htmp

  rw [hmellin]
  by_cases hγ : |γ| ≤ 1
  · calc
      (1 + |γ|) ^ 3 * ‖𝓕 p ξ‖
          ≤ 8 * ‖𝓕 p ξ‖ := by
            have hcube : (1 + |γ|) ^ 3 ≤ (2 : ℝ) ^ 3 := by
              apply pow_le_pow_left₀
              · positivity
              · linarith [abs_nonneg γ]
            norm_num at hcube ⊢
            gcongr
      _ ≤ 8 * L := by gcongr
  · have hγ1 : 1 ≤ |γ| := le_of_not_ge hγ
    have hcube : (1 + |γ|) ^ 3 ≤ 8 * |γ| ^ 3 := by
      have hlin : 1 + |γ| ≤ 2 * |γ| := by linarith
      calc
        (1 + |γ|) ^ 3 ≤ (2 * |γ|) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hlin 3
        _ = 8 * |γ| ^ 3 := by ring
    calc
      (1 + |γ|) ^ 3 * ‖𝓕 p ξ‖
          ≤ (8 * |γ| ^ 3) * ‖𝓕 p ξ‖ := by gcongr
      _ = 8 * (|γ| ^ 3 * ‖𝓕 p ξ‖) := by ring
      _ ≤ 8 * L := by gcongr

/-- Uniform vertical cubic decay implies the existing canonical shell-local
cubic certificate, with the explicit geometric factor eight. -/
theorem uniform_mellin_vertical_cubic_decay_implies_shell_decay_v1
    {f : ℝ → ℂ}
    (h : HasUniformMellinVerticalCubicDecayV1 f) :
    HasCubicShellMellinDecayV1 f := by
  rcases h with ⟨D, hD, hdecay⟩
  refine ⟨8 * D, mul_nonneg (by norm_num) hD, ?_⟩
  intro n rho
  let z : ℂ := rho.1.1
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1 rho.1.2.1 rho.1.2.2
  have hre : z.re ∈ Set.Icc (0 : ℝ) 1 := ⟨hstrip.1.le, hstrip.2.le⟩
  have hs : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by
    apply Complex.ext <;> simp
  have hv := hdecay z.re hre z.im
  rw [hs] at hv

  have hshell : Nat.ceil |z.im| = n := by
    simpa [z, ZeroHeightShellSetV1, ZeroHeightShellIndexV1] using rho.2
  have hceil : (n : ℝ) < |z.im| + 1 := by
    rw [← hshell]
    exact Nat.ceil_lt_add_one (abs_nonneg z.im)
  let t : ℝ := ((n + 1 : ℕ) : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hgeom : t ≤ 2 * (1 + |z.im|) := by
    dsimp [t]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith [abs_nonneg z.im]
  have hgeom3 : t ^ 3 ≤ 8 * (1 + |z.im|) ^ 3 := by
    calc
      t ^ 3 ≤ (2 * (1 + |z.im|)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hgeom 3
      _ = 8 * (1 + |z.im|) ^ 3 := by ring

  have hscaled :
      t ^ 3 * ‖mellin f z‖ ≤ 8 * D := by
    calc
      t ^ 3 * ‖mellin f z‖
          ≤ (8 * (1 + |z.im|) ^ 3) * ‖mellin f z‖ := by gcongr
      _ = 8 * ((1 + |z.im|) ^ 3 * ‖mellin f z‖) := by ring
      _ ≤ 8 * D := by gcongr
  apply (le_div_iff₀' (pow_pos ht 3)).2
  simpa [t, mul_comm] using hscaled

/-- The existing compact-smooth positive-support domain therefore supplies the
actual shell-local cubic Mellin certificate consumed by PR #479. -/
theorem weil_compact_smooth_has_cubic_shell_mellin_decay_v1
    (g : WeilCompactSmoothGV1) :
    HasCubicShellMellinDecayV1 g.1 :=
  uniform_mellin_vertical_cubic_decay_implies_shell_decay_v1
    (weil_compact_smooth_mellin_vertical_cubic_decay_v1 g)

#check HasUniformMellinVerticalCubicDecayV1
#check weil_compact_smooth_mellin_vertical_cubic_decay_v1
#check uniform_mellin_vertical_cubic_decay_implies_shell_decay_v1
#check weil_compact_smooth_has_cubic_shell_mellin_decay_v1
#print axioms weil_compact_smooth_mellin_vertical_cubic_decay_v1
#print axioms uniform_mellin_vertical_cubic_decay_implies_shell_decay_v1
#print axioms weil_compact_smooth_has_cubic_shell_mellin_decay_v1
