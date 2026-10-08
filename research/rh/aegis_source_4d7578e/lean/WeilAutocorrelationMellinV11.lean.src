import WeilPairedZeroEvaluationV9
import WeilWidthArchCorrelationV25
import WeilAutocorrelationClosureV1
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
AEGIS Ω — full Mellin factorization of multiplicative autocorrelation V11.

For a repository packet g, put

  h(u) = exp(u/2) g(exp u),
  C_g(t) = ∫ h(v+t) conj(h(v)) dv,
  H_g(z) = ∫ exp(z u) h(u) du.

This module proves the bilateral correlation-transform identity

  ∫ exp(z t) C_g(t) dt
    = H_g(z) * conj(H_g(-conj z)),

using a genuine product-integrability/Fubini proof on the compact log-support.

Combining this with the existing log-coordinate Mellin representation and
the multiplicative/log autocorrelation identity gives, for every s : ℂ,

  mellin (WeilAutocorrelationV1 g) s
    = mellin g s * conj (mellin g (1 - conj s)).

This is the load-bearing zero-side factorization used by the restricted
Weil-criterion contrapositive.  No sign or RH conclusion is asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Function MeasureTheory Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilAutocorrelationMellinV11

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilPairedZeroEvaluationV9

/-- Centered bilateral Mellin/Laplace transform of the logarithmic packet. -/
def WeilCenteredTransformV11
    (g : WeilCompactSmoothGV1) (z : ℂ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (z * (u : ℂ)) * logLift g.1 u

/-- Exact relation between the centered transform and the repository Mellin
transform. -/
theorem centered_transform_eq_mellin_v11
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    WeilCenteredTransformV11 g z =
      mellin g.1 (z + (1 / 2 : ℂ)) := by
  rw [mellin_eq_log_integral_v9]
  unfold WeilCenteredTransformV11 WeilLogMellinIntegrandV9 logLift
  apply integral_congr_ae
  filter_upwards [] with u
  have hexp :
      Complex.exp ((z + (1 / 2 : ℂ)) * (u : ℂ)) =
        Complex.exp (z * (u : ℂ)) *
          (Real.exp (u / 2) : ℂ) := by
    rw [show
      (z + (1 / 2 : ℂ)) * (u : ℂ) =
        z * (u : ℂ) + ((u / 2 : ℝ) : ℂ) by
          push_cast
          ring,
      Complex.exp_add,
      ← Complex.ofReal_exp]
  rw [hexp]
  ring

private theorem logLift_continuous_v11
    (g : WeilCompactSmoothGV1) :
    Continuous (logLift g.1) := by
    have hg : Continuous g.1 := g.2.1.continuous
    unfold logLift
    fun_prop

/-- Public compact-support fact for the logarithmic packet. -/
theorem logLift_hasCompactSupport_v11
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (logLift g.1) := by
  let K : Set ℝ := Real.log '' tsupport g.1
  have hK : IsCompact K := by
    have hlog : ContinuousOn Real.log (tsupport g.1) := by
      intro x hx
      exact
        (Real.continuousAt_log
          (ne_of_gt (g.2.2.2 hx))).continuousWithinAt
    exact g.2.2.1.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro u hu
  have hne : g.1 (Real.exp u) ≠ 0 := by
    intro hz
    apply hu
    simp [logLift, hz]
  have hm : Real.exp u ∈ tsupport g.1 := subset_tsupport _ hne
  exact ⟨Real.exp u, hm, Real.log_exp u⟩

/-- Joint kernel whose two iterated integrals are exchanged in the
correlation-transform proof. -/
def WeilCenteredCorrelationJointV11
    (g : WeilCompactSmoothGV1) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (z * (p.1 : ℂ)) *
    logLift g.1 (p.2 + p.1) *
      conj (logLift g.1 p.2)

/-- Absolute product-integrability of the centered correlation kernel for every
complex spectral parameter.  Compact support, not a strip estimate, carries
the proof. -/
theorem centered_correlation_joint_integrable_v11
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    Integrable (WeilCenteredCorrelationJointV11 g z)
      (volume.prod volume) := by
  let K : Set ℝ := tsupport (logLift g.1)
  let J : Set (ℝ × ℝ) :=
    (fun p : ℝ × ℝ => (p.1 - p.2, p.2)) '' (K ×ˢ K)
  have hK : IsCompact K := (logLift_hasCompactSupport_v11 g)
  have hJ : IsCompact J := by
    apply hK.prod hK |>.image
    fun_prop
  have hcont : Continuous (WeilCenteredCorrelationJointV11 g z) := by
    unfold WeilCenteredCorrelationJointV11
    exact
      ((by fun_prop :
        Continuous (fun p : ℝ × ℝ =>
          Complex.exp (z * (p.1 : ℂ)))).mul
        ((logLift_continuous_v11 g).comp
          (continuous_snd.add continuous_fst))).mul
        (continuous_conj.comp
          ((logLift_continuous_v11 g).comp continuous_snd))
  have hsupp :
      tsupport (WeilCenteredCorrelationJointV11 g z) ⊆ J := by
    apply closure_minimal ?_ hJ.isClosed
    intro p hp
    have hleft : logLift g.1 (p.2 + p.1) ≠ 0 := by
      intro hz
      apply hp
      simp [WeilCenteredCorrelationJointV11, hz]
    have hright : logLift g.1 p.2 ≠ 0 := by
      intro hz
      apply hp
      simp [WeilCenteredCorrelationJointV11, hz]
    have hl : p.2 + p.1 ∈ K := subset_tsupport _ hleft
    have hr : p.2 ∈ K := subset_tsupport _ hright
    refine ⟨(p.2 + p.1, p.2), ⟨hl, hr⟩, ?_⟩
    apply Prod.ext <;> simp <;> ring
  exact hcont.integrable_of_hasCompactSupport
    (hJ.of_isClosed_subset (isClosed_tsupport _) hsupp)

/-- Inner-u transform at fixed v. -/
private theorem centered_correlation_inner_u_v11
    (g : WeilCompactSmoothGV1) (z : ℂ) (v : ℝ) :
    (∫ u : ℝ,
      Complex.exp (z * (u : ℂ)) *
        logLift g.1 (v + u) *
          conj (logLift g.1 v)) =
      WeilCenteredTransformV11 g z *
        (Complex.exp (-(z * (v : ℂ))) *
          conj (logLift g.1 v)) := by
  let F : ℝ → ℂ := fun w =>
    Complex.exp (z * (w : ℂ)) * logLift g.1 w
  have hshift :
      (∫ u : ℝ,
        Complex.exp (z * (u : ℂ)) *
          logLift g.1 (v + u)) =
        Complex.exp (-(z * (v : ℂ))) *
          WeilCenteredTransformV11 g z := by
    calc
      (∫ u : ℝ,
        Complex.exp (z * (u : ℂ)) *
          logLift g.1 (v + u))
        =
      ∫ u : ℝ,
        Complex.exp (-(z * (v : ℂ))) * F (u + v) := by
          apply integral_congr_ae
          filter_upwards [] with u
          dsimp [F]
          rw [← mul_assoc, ← Complex.exp_add, add_comm u v]
          congr 2
          push_cast
          ring
      _ =
        Complex.exp (-(z * (v : ℂ))) *
          (∫ u : ℝ, F (u + v)) := by
            rw [integral_const_mul]
      _ =
        Complex.exp (-(z * (v : ℂ))) *
          (∫ u : ℝ, F u) := by
            rw [integral_add_right_eq_self F v]
      _ =
        Complex.exp (-(z * (v : ℂ))) *
          WeilCenteredTransformV11 g z := by
            rfl
  rw [integral_mul_const, hshift]
  ring

/-- Conjugated reflected centered transform. -/
private theorem reflected_centered_transform_v11
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      Complex.exp (-(z * (v : ℂ))) *
        conj (logLift g.1 v)) =
      conj (WeilCenteredTransformV11 g (-conj z)) := by
  rw [WeilCenteredTransformV11, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_neg, map_mul, Complex.conj_ofReal]

/-- Bilateral transform of the log-autocorrelation factors exactly. -/
theorem centered_correlation_transform_factorization_v11
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ u : ℝ,
      Complex.exp (z * (u : ℂ)) *
        logCorrelationV25 g u) =
      WeilCenteredTransformV11 g z *
        conj (WeilCenteredTransformV11 g (-conj z)) := by
  have hprod := centered_correlation_joint_integrable_v11 g z
  calc
    (∫ u : ℝ,
      Complex.exp (z * (u : ℂ)) *
        logCorrelationV25 g u)
      =
    ∫ u : ℝ,
      ∫ v : ℝ,
        WeilCenteredCorrelationJointV11 g z (u, v) := by
          apply integral_congr_ae
          filter_upwards [] with u
          unfold logCorrelationV25 WeilCenteredCorrelationJointV11
          rw [← integral_const_mul]
          congr 1
          funext v
          simp only
          ring
    _ =
    ∫ v : ℝ,
      ∫ u : ℝ,
        WeilCenteredCorrelationJointV11 g z (u, v) := by
          exact integral_integral_swap
            (f := fun u v => WeilCenteredCorrelationJointV11 g z (u, v))
            (by simpa [Function.uncurry_def] using hprod)
    _ =
    ∫ v : ℝ,
      WeilCenteredTransformV11 g z *
        (Complex.exp (-(z * (v : ℂ))) *
          conj (logLift g.1 v)) := by
          apply integral_congr_ae
          filter_upwards [] with v
          unfold WeilCenteredCorrelationJointV11
          simpa [add_comm, mul_assoc] using
            centered_correlation_inner_u_v11 g z v
    _ =
      WeilCenteredTransformV11 g z *
        (∫ v : ℝ,
          Complex.exp (-(z * (v : ℂ))) *
            conj (logLift g.1 v)) := by
              rw [integral_const_mul]
    _ =
      WeilCenteredTransformV11 g z *
        conj (WeilCenteredTransformV11 g (-conj z)) := by
              rw [reflected_centered_transform_v11]

/-- Full Mellin factorization of the repository autocorrelation, valid for
every complex s. -/
theorem weil_autocorrelation_mellin_factorization_v11
    (g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilAutocorrelationV1 g) s =
      mellin g.1 s *
        conj (mellin g.1 (1 - conj s)) := by
  let A := WeilAutocorrelationCompactSmoothV1 g
  have hlog :=
    mellin_eq_log_integral_v9 A s
  have hcorr :
      (∫ u : ℝ,
        WeilLogMellinIntegrandV9 A s u) =
      ∫ u : ℝ,
        Complex.exp ((s - (1 / 2 : ℂ)) * (u : ℂ)) *
          logCorrelationV25 g u := by
    apply integral_congr_ae
    filter_upwards [] with u
    unfold WeilLogMellinIntegrandV9
    rw [show A.1 (Real.exp u) = WeilAutocorrelationV1 g (Real.exp u) by rfl]
    rw [logCorrelation_eq_autocorrelation_v25]
    have he :
        (Real.exp (u / 2) : ℂ) ≠ 0 := by simp
    field_simp [he]
    have hsplit :
        Complex.exp (s * (u : ℂ)) =
          Complex.exp ((u : ℂ) * (s * 2 - 1) / 2) *
            Complex.exp (((u / 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Complex.ofReal_exp, hsplit]
    ring
  rw [show mellin (WeilAutocorrelationV1 g) s = mellin A.1 s from rfl, hlog, hcorr,
    centered_correlation_transform_factorization_v11]
  rw [centered_transform_eq_mellin_v11,
    centered_transform_eq_mellin_v11]
  congr 2
  · ring
  · congr 2
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    simp [h2]
    ring

  end AEGIS.WeilAutocorrelationMellinV11

#print axioms AEGIS.WeilAutocorrelationMellinV11.centered_correlation_transform_factorization_v11
#print axioms AEGIS.WeilAutocorrelationMellinV11.weil_autocorrelation_mellin_factorization_v11
