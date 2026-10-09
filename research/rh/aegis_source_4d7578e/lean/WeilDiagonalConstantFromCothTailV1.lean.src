/-
AEGIS Ω — binding the proved coth tail to the width-1/32 diagonal constant, V1.

`WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor` proves

    32449/31500 < 6·log 2 − log(4π) − γ − (1/64)·exp(1/64)

and its docstring states exactly what is missing:

  "The complete elementary constant margin needed AFTER the analytic diagonal
   kernel has been reduced to `log(coth(1/64)) − log(4π) − γ − (1/64) exp(1/64)`.
   NO KERNEL IDENTITY IS ASSERTED HERE."

So `6·log 2` there is a hand-picked rational stand-in for the real archimedean
tail.  `WeilArchimedeanCothTailV1` proves the tail itself:

    ∫_{1/32}^{∞} du / sinh u = log ((1 + e^{-1/32}) / (1 − e^{-1/32}))    and
    6·log 2 < ∫_{1/32}^{∞} du / sinh u.

This module joins the two.  `diagonalConstantV1` is the reduced constant with
the ACTUAL tail integral in place of the stand-in, and
`certificate_threshold_lt_diagonalConstant` shows the certificate's threshold
103/100 is exceeded by it.  `integral_eq_log_coth_one_div_64` identifies the
tail with `log (coth (1/64))` literally, so the object named in the docstring
and the object bounded here are the same object.

WHAT THIS DOES NOT DO

It does not bind the constant to `WeilArchimedeanIntegrandV1` for a concrete
packet.  That step — the packet-level kernel identity, that the archimedean
part of the Weil right side for a concrete width-1/32 test function reduces to
this tail scaled by ‖g‖² — needs a concrete `WeilCompactSmoothGV1` witness with
controlled log-support, the change of variables x = e^u turning (x − x⁻¹) into
2 sinh u, and the autocorrelation vanishing outside that support.  None of
those is proved here.  `ArchimedeanPacketReductionV1` names that obligation; it
is quantified over and NEVER constructed in this module.

`ANALYTIC_DIAGONAL_LOWER_V1` therefore remains OPEN, as do the global Weil sign
and RH.  This module proves no sign and no part of RH.

BUILD NOTE.  This module imports across two lanes that do not currently share
a branch:

  * `WeilArchimedeanCothTailV1.lean`         — `proof/weil-arch-tail-order-lean-v1`
  * `WeilThreeBlockAnalyticConstantsV21.lean` — `proof/weil-analytic-v21-probe`
                                                @ c8021b22, blob 92271bb5

It was compiled with both on the include path.  Neither branch alone resolves
both imports today; that is an integration gap, recorded here rather than
papered over by duplicating a file.
-/
import WeilArchimedeanCothTailV1
import WeilThreeBlockAnalyticConstantsV21

open Set MeasureTheory
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilThreeBlockAnalyticConstantsV21

noncomputable section

namespace AEGIS.WeilDiagonalConstantFromCothTailV1

/-- The reduced diagonal constant, written with the ACTUAL archimedean tail
integral rather than the rational stand-in `6 log 2`. -/
def diagonalConstantV1 : ℝ :=
  (∫ u in Ioi (1 / 32 : ℝ), 1 / Real.sinh u)
    - Real.log (4 * Real.pi)
    - Real.eulerMascheroniConstant
    - ((1 : ℝ) / 64) * Real.exp ((1 : ℝ) / 64)

/-! ### 1. The tail is exactly `log (coth (1/64))` -/

/-- `cosh x / sinh x = (1 + e^{-2x}) / (1 − e^{-2x})` for `x > 0`. -/
theorem cosh_div_sinh_eq {x : ℝ} (hx : 0 < x) :
    Real.cosh x / Real.sinh x
      = (1 + Real.exp (-(2 * x))) / (1 - Real.exp (-(2 * x))) := by
  have hE : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hEne : Real.exp x ≠ 0 := ne_of_gt hE
  have hE1 : 1 < Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have hinv1 : (Real.exp x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hinv0 : (0 : ℝ) < (Real.exp x)⁻¹ := inv_pos.mpr hE
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have h2 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd1 : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := ne_of_gt (by linarith)
  have hd2 : (1 : ℝ) - (Real.exp x)⁻¹ * (Real.exp x)⁻¹ ≠ 0 :=
    ne_of_gt (by nlinarith)
  rw [Real.cosh_eq, Real.sinh_eq, h2, hneg]
  field_simp

/-- The tail at half-width `w = 1/32` IS `log (coth (1/64))` — the constant the
`WeilThreeBlockAnalyticConstantsV21` docstring names. -/
theorem integral_eq_log_coth_one_div_64 :
    (∫ u in Ioi (1 / 32 : ℝ), 1 / Real.sinh u)
      = Real.log (Real.cosh (1 / 64) / Real.sinh (1 / 64)) := by
  rw [integral_one_div_sinh_Ioi (by norm_num : (0 : ℝ) < 1 / 32),
    cosh_div_sinh_eq (by norm_num : (0 : ℝ) < 1 / 64)]
  norm_num

/-! ### 2. The constant binding -/

/-- The certificate's own floor is exceeded once the stand-in `6 log 2` is
replaced by the actual tail integral. -/
theorem floor_lt_diagonalConstant :
    (32449 : ℝ) / 31500 < diagonalConstantV1 := by
  have h1 := diagonal_constant_floor
  have h2 := six_log_two_lt_integral_one_div_sinh_Ioi
  simp only [diagonalConstantV1]
  linarith

/-- **The binding.**  The width-1/32 certificate threshold `103/100` is strictly
below the reduced diagonal constant built from the PROVED archimedean tail. -/
theorem certificate_threshold_lt_diagonalConstant :
    (103 : ℝ) / 100 < diagonalConstantV1 :=
  certificate_diagonal_threshold.trans floor_lt_diagonalConstant

/-- CONTROL: the constant is strictly positive, so the threshold comparison is
not a statement about a negative quantity.  (The tail's own upper bound, `tail
< 7 log 2`, lives in `WeilArchimedeanCothTailV1_Control` and is not restated
here; this theorem asserts positivity only.) -/
theorem diagonalConstant_pos : 0 < diagonalConstantV1 :=
  lt_trans (by norm_num) certificate_threshold_lt_diagonalConstant

/-! ### 3. The remaining obligation, named and never constructed -/

/-- The packet-level kernel identity: for a concrete width-1/32 test function,
the archimedean part `arch` of the Weil right side reduces to the reduced
diagonal constant `D` scaled by the squared norm `nrm2`.

**This is an assumption, not a theorem.**  It is quantified over below and is
never constructed anywhere in this module.  Proving it requires a concrete
`WeilCompactSmoothGV1` witness with controlled log-support, the change of
variables `x = e^u`, and vanishing of the autocorrelation outside that
support. -/
structure ArchimedeanPacketReductionV1 (D nrm2 arch : ℝ) : Prop where
  reduction : arch = D * nrm2
  norm_pos : 0 < nrm2

/-- CONDITIONAL.  *Given* the packet reduction — which is assumed, not proved —
the archimedean part exceeds `(103/100)‖g‖²`, which is the shape
`ANALYTIC_DIAGONAL_LOWER_V1` needs. -/
theorem certificate_threshold_of_packet_reduction {nrm2 arch : ℝ}
    (h : ArchimedeanPacketReductionV1 diagonalConstantV1 nrm2 arch) :
    (103 : ℝ) / 100 * nrm2 < arch := by
  rw [h.reduction]
  exact mul_lt_mul_of_pos_right certificate_threshold_lt_diagonalConstant h.norm_pos

/-- CONTROL (non-vacuity): the obligation is satisfiable, so the conditional
theorem above is not vacuously true.  Exhibiting a satisfying triple is NOT the
same as discharging the obligation for an actual test function. -/
theorem packet_reduction_not_vacuous :
    ∃ nrm2 arch : ℝ, ArchimedeanPacketReductionV1 diagonalConstantV1 nrm2 arch :=
  ⟨1, diagonalConstantV1, ⟨by ring, one_pos⟩⟩

end AEGIS.WeilDiagonalConstantFromCothTailV1

#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.cosh_div_sinh_eq
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.integral_eq_log_coth_one_div_64
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.floor_lt_diagonalConstant
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.certificate_threshold_lt_diagonalConstant
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.diagonalConstant_pos
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.certificate_threshold_of_packet_reduction
#print axioms AEGIS.WeilDiagonalConstantFromCothTailV1.packet_reduction_not_vacuous
