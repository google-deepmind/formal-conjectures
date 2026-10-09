import WeilDiagonalKernelReductionV21
import WeilWidthPrimeVanishingV23
import WeilArchimedeanCothTailV1

/-!
AEGIS Ω — width-1/32 diagonal Archimedean frontier V2.4.

This module composes three already separately verified pieces:
1. exact width-1/32 diagonal prime-sum vanishing;
2. the symbolic actual-repository diagonal reduction;
3. the explicit coth-tail theorem at w = 1/32.

The result discharges the discrete prime term and the tail threshold in the
103/100 diagonal estimate.  Exactly one analytic premise remains: the
Archimedean integral budget identifying the actual repository Archimedean
kernel with the small-minus-tail bound.

No off-diagonal bound, universal sign, global Weil positivity, or RH result is
asserted here.
-/

open Set MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilWidthDiagonalArchFrontierV24

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthPrimeVanishingV23
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilArchimedeanCothTailV1

/-- The exact width-1/32 Archimedean tail used by the retained diagonal
certificate. -/
def diagonalTailV24 : ℝ :=
  ∫ u in Ioi (1 / 32 : ℝ), 1 / Real.sinh u

/-- The coth-tail theorem discharges the retained certificate threshold. -/
theorem diagonal_tail_gt_six_log_two_v24 :
    6 * Real.log 2 < diagonalTailV24 := by
  simpa [diagonalTailV24] using
    AEGIS.WeilArchimedeanCothTailV1.six_log_two_lt_integral_one_div_sinh_Ioi

/-- Width support discharges the entire diagonal prime contribution. -/
theorem width_diagonal_prime_sum_zero_v24
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0 :=
  AEGIS.WeilWidthPrimeVanishingV23.diagonal_prime_sum_zero g a hw

/-- The exact load-bearing diagonal frontier.

After the already verified prime and coth-tail transitions are composed, the
103/100 coercive diagonal estimate follows from one and only one remaining
analytic statement: the actual Archimedean integral budget below. -/
theorem width_diagonal_103_over_100_of_arch_budget_v24
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (harch :
      (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
        energy g.1 * (diagonalSmallV21 - diagonalTailV24)) :
    (103 / 100 : ℝ) * energy g.1 ≤ -(B g g).re := by
  exact
    actual_diagonal_103_over_100
      g diagonalTailV24
      (width_diagonal_prime_sum_zero_v24 g a hw)
      (le_of_lt diagonal_tail_gt_six_log_two_v24)
      harch

end AEGIS.WeilWidthDiagonalArchFrontierV24

#print axioms AEGIS.WeilWidthDiagonalArchFrontierV24.diagonal_tail_gt_six_log_two_v24
#print axioms AEGIS.WeilWidthDiagonalArchFrontierV24.width_diagonal_prime_sum_zero_v24
#print axioms AEGIS.WeilWidthDiagonalArchFrontierV24.width_diagonal_103_over_100_of_arch_budget_v24
