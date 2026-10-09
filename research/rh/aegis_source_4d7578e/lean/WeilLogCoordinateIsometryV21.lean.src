import WeilAutocorrelationClosureV1
import WeilDisjointEnergyV2
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
AEGIS Ω — logarithmic-coordinate L2 isometry bridge V2.1

LOCAL CANDIDATE / FORMAL_MATH_EVIDENCE_ONLY / NOT_YET_KERNEL_REPLAYED.

For a repository packet `g`, define

  h(t) = exp(t/2) * g(exp t).

The intended certificate normalization is `H = ∫ ||h(t)||² dt`.
This module proves the change-of-variables statement needed to identify it
with the repository's ordinary Lebesgue L2 energy of `g`, using the actual
positive-support invariant of `WeilCompactSmoothGV1`.

It does NOT prove any diagonal/off-diagonal Weil estimate, global sign, or RH.
-/

open Set Function MeasureTheory Complex
open scoped ContDiff ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilLogCoordinateIsometryV21

open AEGIS.WeilDisjointEnergyV2

def logLift (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.ofReal (Real.exp (t / 2)) * g (Real.exp t)

/-- Whole-line exponential substitution, derived directly from Mathlib's
one-dimensional Jacobian theorem. -/
theorem integral_exp_substitution (f : ℝ → ℝ) :
    (∫ t : ℝ, Real.exp t * f (Real.exp t)) =
      ∫ x in Ioi (0 : ℝ), f x := by
  have hcov :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (f := Real.exp)
      (f' := Real.exp)
      (s := Set.univ)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Set.injOn_of_injective Real.exp_injective)
      f
  have himage : Real.exp '' Set.univ = Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  rw [himage] at hcov
  simpa [abs_of_pos (Real.exp_pos _)] using hcov.symm

theorem logLift_norm_sq (g : ℝ → ℂ) (t : ℝ) :
    ‖logLift g t‖ ^ 2 =
      Real.exp t * ‖g (Real.exp t)‖ ^ 2 := by
  have hexp :
      (Real.exp (t / 2)) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [logLift, norm_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, hexp]

/-- The certificate's additive-coordinate energy is exactly the positive-axis
energy of the multiplicative packet. -/
theorem logLift_energy_eq_positive_energy (g : ℝ → ℂ) :
    (∫ t : ℝ, ‖logLift g t‖ ^ 2) =
      ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2 := by
  calc
    (∫ t : ℝ, ‖logLift g t‖ ^ 2)
        = ∫ t : ℝ, Real.exp t * ‖g (Real.exp t)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with t
            exact logLift_norm_sq g t
    _ = ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2 :=
      integral_exp_substitution (fun x : ℝ => ‖g x‖ ^ 2)

/-- Because a repository Weil packet has topological support inside `(0,∞)`,
its full-line L2 energy equals its positive-axis L2 energy. -/
theorem packet_energy_eq_positive_energy (g : WeilCompactSmoothGV1) :
    energy g.1 = ∫ x in Ioi (0 : ℝ), ‖g.1 x‖ ^ 2 := by
  unfold energy
  simpa using
    (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (f := fun x : ℝ => ‖g.1 x‖ ^ 2)
      (s := Ioi (0 : ℝ))
      (t := Set.univ)
      MeasurableSet.univ
      (Set.subset_univ _)
      (by
        intro x hx
        have hxnot : x ∉ tsupport g.1 := by
          intro hxt
          exact hx.2 (g.2.2.2 hxt)
        have hg0 : g.1 x = 0 := image_eq_zero_of_notMem_tsupport hxnot
        simp [hg0]))

/-- Exact norm identification required by the quotient-free three-block work
order: `H = ||h||₂² = energy(g)`. -/
theorem logLift_energy_eq_packet_energy (g : WeilCompactSmoothGV1) :
    (∫ t : ℝ, ‖logLift g.1 t‖ ^ 2) = energy g.1 := by
  calc
    (∫ t : ℝ, ‖logLift g.1 t‖ ^ 2)
        = ∫ x in Ioi (0 : ℝ), ‖g.1 x‖ ^ 2 :=
      logLift_energy_eq_positive_energy g.1
    _ = energy g.1 := (packet_energy_eq_positive_energy g).symm

end AEGIS.WeilLogCoordinateIsometryV21
