import WeilMixedAlgebraV2
import WeilLogCoordinateIsometryV21
import WeilThreeBlockAnalyticConstantsV21

/-!
AEGIS Ω — width-1/32 diagonal symbolic reduction V2.1

FORMAL_MATH_EVIDENCE_ONLY.

This module binds the diagonal bookkeeping to the ACTUAL repository mixed form
`B`, without dividing by the packet energy.  It deliberately leaves the hard
continuous analysis as explicit hypotheses.

It does NOT prove:
* diagonal prime-sum vanishing for a width-1/32 packet;
* the Archimedean kernel integral inequality;
* the coth/tail lower bound;
* the six actual B-bounds;
* global Weil sign or RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDiagonalKernelReductionV21

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21

def diagonalKappaV21 : ℝ :=
  Real.log (4 * Real.pi) + Real.eulerMascheroniConstant

def diagonalSmallV21 : ℝ :=
  ((1 : ℝ) / 64) * Real.exp ((1 : ℝ) / 64)

/-- At the identity, the real part of the repository autocorrelation is exactly
its ordinary Lebesgue L2 energy. -/
theorem autocorrelation_one_re_eq_energy
    (g : WeilCompactSmoothGV1) :
    (WeilAutocorrelationV1 g 1).re = energy g.1 := by
  have hint :
      IntegrableOn (fun y : ℝ => g.1 y * star (g.1 y)) (Ioi 0) := by
    simpa only [one_mul] using
      (weil_autocorrelation_integrand_integrable_v1 g 1)
  rw [packet_energy_eq_positive_energy g]
  unfold WeilAutocorrelationV1
  simp only [one_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  calc
    (g.1 y * star (g.1 y)).re = Complex.normSq (g.1 y) := by
      have hmul := congrArg Complex.re (Complex.mul_conj (g.1 y))
      simpa only [Complex.star_def, Complex.ofReal_re] using hmul
    _ = ‖g.1 y‖ ^ 2 := Complex.normSq_eq_norm_sq (g.1 y)

/-- If the diagonal prime part vanishes, the real part of the ACTUAL repository
mixed form is kappa times the actual packet energy plus the real Archimedean
integral. -/
theorem actual_diagonal_rhs_decomposition
    (g : WeilCompactSmoothGV1)
    (hprime : WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0) :
    (B g g).re =
      diagonalKappaV21 * energy g.1 +
        (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re := by
  unfold B
  rw [diagonal_eq]
  unfold WeilExplicitRightSideV1
  rw [hprime]
  have hcenter := autocorrelation_one_re_eq_energy g
  simp only [zero_add, Complex.add_re]
  unfold WeilArchimedeanConstantV1 diagonalKappaV21
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hcenter]

/-- Pure quotient-free reduction.  The difficult continuous estimate is kept
as one explicit Archimedean premise. -/
theorem actual_diagonal_from_arch_budget
    (g : WeilCompactSmoothGV1)
    (tail small : ℝ)
    (hprime : WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0)
    (harch :
      (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
        energy g.1 * (small - tail)) :
    energy g.1 * (tail - diagonalKappaV21 - small) ≤ -(B g g).re := by
  rw [actual_diagonal_rhs_decomposition g hprime]
  nlinarith

/-- Once the width-1/32 tail dominates `6 log 2`, the already kernel-verified
constant layer converts the symbolic analytic budget into the exact diagonal
hypothesis consumed by `actual_three_block_bound`. -/
theorem actual_diagonal_103_over_100
    (g : WeilCompactSmoothGV1)
    (tail : ℝ)
    (hprime : WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0)
    (htail : 6 * Real.log 2 ≤ tail)
    (harch :
      (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
        energy g.1 * (diagonalSmallV21 - tail)) :
    (103 / 100 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hbase :
      (103 / 100 : ℝ) <
        6 * Real.log 2 - diagonalKappaV21 - diagonalSmallV21 := by
    unfold diagonalKappaV21 diagonalSmallV21
    nlinarith [certificate_diagonal_threshold, diagonal_constant_floor]
  have hshift :
      6 * Real.log 2 - diagonalKappaV21 - diagonalSmallV21 ≤
        tail - diagonalKappaV21 - diagonalSmallV21 := by
    linarith
  have hconst := mul_le_mul_of_nonneg_left hbase.le hE
  have htailmul := mul_le_mul_of_nonneg_left hshift hE
  have hanalytic :=
    actual_diagonal_from_arch_budget
      g tail diagonalSmallV21 hprime harch
  calc
    (103 / 100 : ℝ) * energy g.1
        = energy g.1 * (103 / 100 : ℝ) := by ring
    _ ≤ energy g.1 *
          (6 * Real.log 2 - diagonalKappaV21 - diagonalSmallV21) := hconst
    _ ≤ energy g.1 *
          (tail - diagonalKappaV21 - diagonalSmallV21) := htailmul
    _ ≤ -(B g g).re := hanalytic

end AEGIS.WeilDiagonalKernelReductionV21
