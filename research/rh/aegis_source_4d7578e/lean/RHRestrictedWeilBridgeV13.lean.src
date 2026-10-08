import RestrictedWeilCriterionFinalV13
import RestrictedWeilCriterionResidueCoefficientV11
import RHZeroKernelLaplaceAnalyticV12
import RHMillenniumGateV10
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-!
AEGIS Ω — restricted-Weil bridge V13: final sign implies RH.

Assembly of the already kernel-checked pieces:

* `RHZeroKernelLaplaceV12`: on `Re w > 1/2` the Laplace transform of the
  zero translation kernel equals the resolvent sum `∑ a_ρ / (w - λ_ρ)`;
* `RHZeroKernelLaplaceAnalyticV12`: under the final sign residual the Laplace
  transform is holomorphic on all of `Re w > 0`;
* `RestrictedWeilCriterionResidueCoefficientV11`: for every nontrivial zero
  there is a moment-zero packet with nonzero coefficient `a_ρ`;
* `RestrictedWeilCriterionFinalV13`: a function continuous at `z` cannot agree
  near `z` with a nonzero simple pole plus a continuous function.

New here:

1. the resolvent sum is analytic away from the centered zeros
   (local Weierstrass M-test);
2. `{Re w > 0}` minus the countable set of centered zeros is path connected
   (transport of Mathlib's countable-complement theorem through the
   homeomorphism `x + iy ↦ log x + iy`);
3. the identity principle extends the Laplace/resolvent identity to that
   domain;
4. a zero with `Re ρ > 1/2` would produce a genuine simple pole of the Laplace
   transform inside its domain of holomorphy — contradiction;
5. the functional equation reflects the remaining zeros.

Result: `FinalSignResidualV1 → RiemannHypothesis`, hence
`RiemannHypothesis ↔ UniversalZeroQuadraticNonnegativeV10`.

This closes the `restricted_criterion` field of `RHMillenniumCertificateV10`.
It does NOT prove RH: the remaining field `universal_zero_quadratic` is
exactly RH-equivalent.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHRestrictedWeilBridgeV13

open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.RHFinalClosureV1
open AEGIS.RestrictedWeilCriterionFinalV13
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RHMillenniumGateV10

/-! ### Elementary facts about the centered zeros -/

theorem centered_re_v13 (rho : RiemannNontrivialZeroIndexV2) :
    (WeilCenteredZeroExponentV12 rho).re = rho.1.re - 1 / 2 := by
  unfold WeilCenteredZeroExponentV12
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  simp [Complex.sub_re]

/-- Every point of the open right half-plane that is not a centered zero is at
positive distance from all centered zeros. -/
theorem exists_sep_of_not_centered_zero_v13 (w0 : ℂ) (hw0 : 0 < w0.re)
    (hnot : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        ε ≤ ‖w0 - WeilCenteredZeroExponentV12 rho‖ := by
  let s0 : ℂ := w0 + ((1 / 2 : ℝ) : ℂ)
  have hs0 : s0 ∉ riemannZetaZeros := by
    intro hz
    rw [mem_riemannZetaZeros] at hz
    have hnt : ¬ ∃ n : ℕ, s0 = -(2 : ℂ) * (n + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp [s0] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    apply hnot ⟨s0, hz, hnt⟩
    unfold WeilCenteredZeroExponentV12
    simp only [s0]
    push_cast
    ring
  have hopen : IsOpen riemannZetaZerosᶜ := isClosed_riemannZetaZeros.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s0 hs0
  refine ⟨ε, hε, fun rho => ?_⟩
  have hmem : rho.1 ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr rho.2.1
  have hnotball : rho.1 ∉ Metric.ball s0 ε := fun h => hball h hmem
  rw [Metric.mem_ball, not_lt, dist_eq_norm] at hnotball
  have heq : rho.1 - s0 = -(w0 - WeilCenteredZeroExponentV12 rho) := by
    unfold WeilCenteredZeroExponentV12
    simp only [s0]
    push_cast
    ring
  rw [heq, norm_neg] at hnotball
  exact hnotball

/-- Each centered zero is isolated among the centered zeros. -/
theorem exists_sep_of_centered_zero_v13 (rho0 : RiemannNontrivialZeroIndexV2) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ rho : RiemannNontrivialZeroIndexV2, rho ≠ rho0 →
        ε ≤ ‖WeilCenteredZeroExponentV12 rho0 -
          WeilCenteredZeroExponentV12 rho‖ := by
  have hrhoZ : rho0.1 ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr rho0.2.1
  obtain ⟨ε, hε, hball⟩ :=
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete isDiscrete_riemannZetaZeros hrhoZ
  refine ⟨ε, hε, fun rho hne => ?_⟩
  have hval : rho.1 ≠ rho0.1 := fun h => hne (Subtype.ext h)
  have hZ : rho.1 ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr rho.2.1
  have hnotball : rho.1 ∉ Metric.ball rho0.1 ε := by
    intro hb
    have : rho.1 ∈ Metric.ball rho0.1 ε ∩ riemannZetaZeros := ⟨hb, hZ⟩
    rw [hball] at this
    exact hval (by simpa using this)
  rw [Metric.mem_ball, not_lt, dist_eq_norm] at hnotball
  have heq : rho.1 - rho0.1 =
      -(WeilCenteredZeroExponentV12 rho0 - WeilCenteredZeroExponentV12 rho) := by
    unfold WeilCenteredZeroExponentV12
    ring
  rw [heq, norm_neg] at hnotball
  exact hnotball

/-! ### Generic resolvent sums are analytic away from the poles -/

/-- Resolvent sum with an arbitrary coefficient family. -/
def ResolventSumV13 (b : RiemannNontrivialZeroIndexV2 → ℂ) (w : ℂ) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    b rho / (w - WeilCenteredZeroExponentV12 rho)

theorem resolventSum_analyticAt_v13
    (b : RiemannNontrivialZeroIndexV2 → ℂ)
    (hb : Summable (fun rho => ‖b rho‖))
    (w0 : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ rho, b rho ≠ 0 →
      ε ≤ ‖w0 - WeilCenteredZeroExponentV12 rho‖) :
    AnalyticAt ℂ (ResolventSumV13 b) w0 := by
  let U : Set ℂ := Metric.ball w0 (ε / 2)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hw0U : w0 ∈ U := Metric.mem_ball_self (by positivity)
  have hlow : ∀ rho, b rho ≠ 0 → ∀ w ∈ U,
      ε / 2 ≤ ‖w - WeilCenteredZeroExponentV12 rho‖ := by
    intro rho hb0 w hw
    have hd : ‖w - w0‖ < ε / 2 := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hw
    have h1 := hsep rho hb0
    have htri := norm_sub_le_norm_sub_add_norm_sub w0 w
      (WeilCenteredZeroExponentV12 rho)
    rw [norm_sub_rev w0 w] at htri
    linarith
  have hterm : ∀ rho, DifferentiableOn ℂ
      (fun w => b rho / (w - WeilCenteredZeroExponentV12 rho)) U := by
    intro rho
    by_cases hb0 : b rho = 0
    · simp [hb0]
    · intro w hw
      have hne : w - WeilCenteredZeroExponentV12 rho ≠ 0 := by
        intro h
        have := hlow rho hb0 w hw
        rw [h, norm_zero] at this
        linarith
      have hdiff : DifferentiableAt ℂ
          (fun y : ℂ => b rho / (y - WeilCenteredZeroExponentV12 rho)) w := by
        fun_prop (disch := exact hne)
      exact hdiff.differentiableWithinAt
  have hbound : ∀ rho, ∀ w ∈ U,
      ‖b rho / (w - WeilCenteredZeroExponentV12 rho)‖ ≤ (2 / ε) * ‖b rho‖ := by
    intro rho w hw
    by_cases hb0 : b rho = 0
    · simp [hb0]
    · rw [norm_div]
      have hl := hlow rho hb0 w hw
      have hpos : 0 < ‖w - WeilCenteredZeroExponentV12 rho‖ :=
        lt_of_lt_of_le (by positivity) hl
      rw [div_le_iff₀ hpos]
      have h2 : (2 / ε) * (ε / 2) = 1 := by
        rw [div_mul_div_comm, mul_comm 2 ε, div_self (by positivity)]
      calc
        ‖b rho‖ = ‖b rho‖ * ((2 / ε) * (ε / 2)) := by rw [h2, mul_one]
        _ = (2 / ε * ‖b rho‖) * (ε / 2) := by ring
        _ ≤ (2 / ε * ‖b rho‖) * ‖w - WeilCenteredZeroExponentV12 rho‖ := by
          gcongr
  have hmaj : Summable (fun rho => (2 / ε) * ‖b rho‖) := hb.mul_left _
  have hdiff :=
    Complex.differentiableOn_tsum_of_summable_norm hmaj hterm hUopen hbound
  exact hdiff.analyticAt (hUopen.mem_nhds hw0U)

/-! ### The bridge domain and its connectedness -/

def CenteredZeroSetV13 : Set ℂ :=
  Set.range (fun rho : RiemannNontrivialZeroIndexV2 => WeilCenteredZeroExponentV12 rho)

def BridgeDomainV13 : Set ℂ := {w : ℂ | 0 < w.re} \ CenteredZeroSetV13

/-- Logarithmic chart of the right half-plane. -/
def LogChartV13 (w : ℂ) : ℂ := ((Real.log w.re : ℝ) : ℂ) + (w.im : ℂ) * I

/-- Exponential parametrisation of the right half-plane. -/
def ExpChartV13 (z : ℂ) : ℂ := ((Real.exp z.re : ℝ) : ℂ) + (z.im : ℂ) * I

theorem expChart_re_v13 (z : ℂ) : (ExpChartV13 z).re = Real.exp z.re := by
  simp [ExpChartV13, Complex.exp_ofReal_re]

theorem expChart_im_v13 (z : ℂ) : (ExpChartV13 z).im = z.im := by
  simp [ExpChartV13]

theorem logChart_expChart_v13 (z : ℂ) : LogChartV13 (ExpChartV13 z) = z := by
  apply Complex.ext
  · simp [LogChartV13, ExpChartV13, Complex.exp_ofReal_re, Real.log_exp]
  · simp [LogChartV13, ExpChartV13]

theorem expChart_logChart_v13 {w : ℂ} (hw : 0 < w.re) :
    ExpChartV13 (LogChartV13 w) = w := by
  apply Complex.ext
  · simp [LogChartV13, ExpChartV13, Real.exp_log hw]
  · simp [LogChartV13, ExpChartV13]

theorem expChart_continuous_v13 : Continuous ExpChartV13 := by
  unfold ExpChartV13
  fun_prop

theorem bridgeDomain_eq_image_v13 :
    BridgeDomainV13 =
      ExpChartV13 '' (LogChartV13 '' (CenteredZeroSetV13 ∩ {w : ℂ | 0 < w.re}))ᶜ := by
  ext w
  constructor
  · rintro ⟨hw, hnot⟩
    have hwre : 0 < w.re := hw
    refine ⟨LogChartV13 w, ?_, expChart_logChart_v13 hwre⟩
    rintro ⟨s, ⟨hsS, hsre⟩, hs⟩
    have hsre' : 0 < s.re := hsre
    have hre : Real.log w.re = Real.log s.re := by
      have := congrArg Complex.re hs
      simpa [LogChartV13] using this.symm
    have him : w.im = s.im := by
      have := congrArg Complex.im hs
      simpa [LogChartV13] using this.symm
    have hre' : w.re = s.re :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hwre) (Set.mem_Ioi.mpr hsre') hre
    have hws : w = s := Complex.ext hre' him
    exact hnot (hws ▸ hsS)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · show 0 < (ExpChartV13 z).re
      rw [expChart_re_v13]
      exact Real.exp_pos _
    · intro hmem
      apply hz
      refine ⟨ExpChartV13 z, ⟨hmem, ?_⟩, logChart_expChart_v13 z⟩
      show 0 < (ExpChartV13 z).re
      rw [expChart_re_v13]
      exact Real.exp_pos _

theorem bridgeDomain_isPreconnected_v13 : IsPreconnected BridgeDomainV13 := by
  have hcount :
      (LogChartV13 '' (CenteredZeroSetV13 ∩ {w : ℂ | 0 < w.re})).Countable :=
    ((Set.countable_range _).mono Set.inter_subset_left).image _
  have hpath :
      IsPathConnected
        (LogChartV13 '' (CenteredZeroSetV13 ∩ {w : ℂ | 0 < w.re}))ᶜ :=
    hcount.isPathConnected_compl_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat)
  rw [bridgeDomain_eq_image_v13]
  exact (hpath.image expChart_continuous_v13).isConnected.isPreconnected

theorem one_mem_bridgeDomain_v13 : (1 : ℂ) ∈ BridgeDomainV13 := by
  refine ⟨by simp, ?_⟩
  rintro ⟨rho, hrho⟩
  have hre := congrArg Complex.re hrho
  rw [centered_re_v13] at hre
  have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  simp at hre
  linarith [hs.2]

/-! ### Identity principle: Laplace transform equals the resolvent on the domain -/

theorem resolvent_eq_resolventSum_v13 (g : WeilCompactSmoothGV1) :
    WeilZeroResolventV12 g = ResolventSumV13 (WeilZeroCoefficientV11 g) := rfl

theorem laplace_eq_resolvent_on_domain_v13
    (h : FinalSignResidualV1) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    EqOn (WeilZeroKernelLaplaceV12 g) (WeilZeroResolventV12 g) BridgeDomainV13 := by
  have hL : AnalyticOnNhd ℂ (WeilZeroKernelLaplaceV12 g) BridgeDomainV13 :=
    (zero_kernel_laplace_analyticOnNhd_v12 h g hm).mono (fun w hw => hw.1)
  have hR : AnalyticOnNhd ℂ (WeilZeroResolventV12 g) BridgeDomainV13 := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    rw [resolvent_eq_resolventSum_v13]
    exact resolventSum_analyticAt_v13 (WeilZeroCoefficientV11 g)
      (zero_coefficient_norm_summable_v12 g) w hε (fun rho _ => hsep rho)
  refine hL.eqOn_of_preconnected_of_eventuallyEq hR bridgeDomain_isPreconnected_v13
    one_mem_bridgeDomain_v13 ?_
  have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hmem : {w : ℂ | (1 / 2 : ℝ) < w.re} ∈ 𝓝 (1 : ℂ) :=
    hopen.mem_nhds (by simp; norm_num)
  filter_upwards [hmem] with w hw
  exact zero_kernel_laplace_eq_resolvent_v12 g w hw

/-! ### The pole contradiction -/

theorem zero_re_le_half_of_final_sign_v13
    (h : FinalSignResidualV1) (rho0 : RiemannNontrivialZeroIndexV2) :
    rho0.1.re ≤ 1 / 2 := by
  by_contra hlt
  have hlt' : 1 / 2 < rho0.1.re := lt_of_not_ge hlt
  set z : ℂ := WeilCenteredZeroExponentV12 rho0 with hz
  have hzpos : 0 < z.re := by
    rw [hz, centered_re_v13]
    linarith
  obtain ⟨g, hm, ha⟩ := exists_nonzero_zero_coefficient_v11 rho0
  have ha' : WeilZeroCoefficientV11 g rho0 ≠ 0 := ha
  classical
  let a : RiemannNontrivialZeroIndexV2 → ℂ := WeilZeroCoefficientV11 g
  let b : RiemannNontrivialZeroIndexV2 → ℂ := fun rho => if rho = rho0 then 0 else a rho
  have hb : Summable (fun rho => ‖b rho‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun rho => ?_)
      (zero_coefficient_norm_summable_v12 g)
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
      exact le_rfl
  obtain ⟨ε₁, hε₁, hiso⟩ := exists_sep_of_centered_zero_v13 rho0
  have hH : AnalyticAt ℂ (ResolventSumV13 b) z := by
    refine resolventSum_analyticAt_v13 b hb z hε₁ (fun rho hb0 => ?_)
    have hne : rho ≠ rho0 := by
      intro heq
      apply hb0
      simp [b, heq]
    exact hiso rho hne
  have hLc : ContinuousAt (WeilZeroKernelLaplaceV12 g) z :=
    (zero_kernel_laplace_analyticOnNhd_v12 h g hm z hzpos).continuousAt
  -- pointwise split of the resolvent on the bridge domain
  have hsplit : ∀ w ∈ BridgeDomainV13,
      WeilZeroResolventV12 g w = a rho0 / (w - z) + ResolventSumV13 b w := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    have hs : Summable (fun rho => a rho / (w - WeilCenteredZeroExponentV12 rho)) := by
      refine Summable.of_norm_bounded
        ((zero_coefficient_norm_summable_v12 g).mul_left (1 / ε)) (fun rho => ?_)
      rw [norm_div]
      have hl := hsep rho
      have hpos : 0 < ‖w - WeilCenteredZeroExponentV12 rho‖ := lt_of_lt_of_le hε hl
      rw [div_le_iff₀ hpos]
      calc
        ‖a rho‖ = (1 / ε * ‖a rho‖) * ε := by field_simp
        _ ≤ (1 / ε * ‖a rho‖) * ‖w - WeilCenteredZeroExponentV12 rho‖ := by
          gcongr
    unfold WeilZeroResolventV12 ResolventSumV13
    rw [hs.tsum_eq_add_tsum_ite rho0]
    congr 1
    apply tsum_congr
    intro rho
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
  -- punctured neighbourhood of z inside the bridge domain
  let δ : ℝ := min ε₁ z.re
  have hδ : 0 < δ := lt_min hε₁ hzpos
  have hnear : ∀ w ∈ Metric.ball z δ, w ≠ z → w ∈ BridgeDomainV13 := by
    intro w hw hne
    have hd : ‖w - z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_⟩
    · show 0 < w.re
      have hreabs : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hlo := (abs_lt.mp (lt_of_le_of_lt hreabs hd)).1
      have hmin : δ ≤ z.re := min_le_right _ _
      linarith
    · rintro ⟨rho, hrho⟩
      have hrho' : WeilCenteredZeroExponentV12 rho = w := hrho
      have hne' : rho ≠ rho0 := by
        intro heq
        apply hne
        rw [← hrho', heq]
      have h1 := hiso rho hne'
      have hmin : δ ≤ ε₁ := min_le_left _ _
      rw [hrho', norm_sub_rev, ← hz] at h1
      linarith
  have heq : WeilZeroKernelLaplaceV12 g =ᶠ[𝓝[≠] z]
      fun w => a rho0 / (w - z) + ResolventSumV13 b w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      self_mem_nhdsWithin] with w hw hne
    have hwz : w ≠ z := by simpa using hne
    have hwD := hnear w hw hwz
    rw [laplace_eq_resolvent_on_domain_v13 h g hm hwD, hsplit w hwD]
  exact continuous_cannot_equal_nonzero_simple_pole_v13 hLc hH.continuousAt ha' heq

/-! ### Reflection and the Riemann Hypothesis -/

theorem exists_reflected_zero_v13 (rho : RiemannNontrivialZeroIndexV2) :
    ∃ sigma : RiemannNontrivialZeroIndexV2, sigma.1 = 1 - rho.1 := by
  have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hnat : ∀ n : ℕ, rho.1 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hs.1]
  have hone : rho.1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hs.2]
  have hzero : riemannZeta (1 - rho.1) = 0 := by
    rw [riemannZeta_one_sub hnat hone, rho.2.1, mul_zero]
  have hnt : ¬ ∃ n : ℕ, 1 - rho.1 = -(2 : ℂ) * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hs.2]
  exact ⟨⟨1 - rho.1, hzero, hnt⟩, rfl⟩

/-- The final sign residual forces every nontrivial zero onto the critical
line. -/
theorem final_sign_implies_rh_v13 (h : FinalSignResidualV1) : RiemannHypothesis := by
  intro s hz hnt _
  let rho : RiemannNontrivialZeroIndexV2 := ⟨s, hz, hnt⟩
  have h1 : s.re ≤ 1 / 2 := zero_re_le_half_of_final_sign_v13 h rho
  obtain ⟨sigma, hsig⟩ := exists_reflected_zero_v13 rho
  have h2 := zero_re_le_half_of_final_sign_v13 h sigma
  rw [hsig] at h2
  simp at h2
  linarith

/-- The formal restricted-Weil bridge target of the Millennium gate. -/
theorem restricted_weil_criterion_kernel_bridge_v13 :
    RestrictedWeilCriterionKernelBridgeV10 := by
  intro hU
  exact final_sign_implies_rh_v13 (universal_zero_quadratic_iff_final_sign_v10.mp hU)

/-- The Millennium certificate now needs exactly one field. -/
theorem millennium_certificate_of_universal_v13
    (hU : UniversalZeroQuadraticNonnegativeV10) : RHMillenniumCertificateV10 :=
  ⟨hU, restricted_weil_criterion_kernel_bridge_v13⟩

theorem millennium_moment_iff_universal_v13 :
    MillenniumMomentReachedV10 ↔ UniversalZeroQuadraticNonnegativeV10 :=
  ⟨fun ⟨cert⟩ => cert.universal_zero_quadratic,
    fun hU => ⟨millennium_certificate_of_universal_v13 hU⟩⟩

end AEGIS.RHRestrictedWeilBridgeV13

#print axioms AEGIS.RHRestrictedWeilBridgeV13.resolventSum_analyticAt_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.bridgeDomain_isPreconnected_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.laplace_eq_resolvent_on_domain_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.zero_re_le_half_of_final_sign_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13
#print axioms AEGIS.RHRestrictedWeilBridgeV13.millennium_moment_iff_universal_v13
