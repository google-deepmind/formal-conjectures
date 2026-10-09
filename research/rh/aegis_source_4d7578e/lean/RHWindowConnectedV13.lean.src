import RHHatCoxClass693V13
import WeilWindowExhaustionV1
import RHRestrictedWeilBridgeV13
import Mathlib.Tactic

/-!
AEGIS Ω — the connected window chain to RH, V13.

Connects four kernel-checked results already in the repository:

* `RHHatCoxClass693V13.hat_coercive`: every moment-zero packet of log-half-width
  `≤ 693/2000` has `Re RHS ≤ −E/200`;
* `WeilWindowExhaustionV1`: universal arithmetic nonpositivity ⇔ nonpositivity on every
  finite symmetric log window `[−L, L]` (monotone in `L`; positive integers suffice);
* `RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13 : FinalSignResidualV1 → RiemannHypothesis`.

Result: the window `693/2000` (and every smaller one) is discharged, and RH follows from
the sign on the windows `L > 693/2000` alone, or equivalently on the integer windows.
Those remaining windows are NOT proved here.  No RH claim.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowConnectedV13

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHHatCoxClass693V13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.RHFinalClosureV1
open AEGIS.RHRestrictedWeilBridgeV13

/-- The window `[−693/2000, 693/2000]` is closed (kernel, via the Coxeter hat class). -/
theorem window_693_arithmetic_nonpositive :
    WindowArithmeticNonpositiveV1 (693 / 2000) := by
  intro g hm hwindow
  have hw : HalfWidthAt g (693 / 2000) 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  have hc := hat_coercive g 0 hw hm
  have hE := energy_nonnegative g.1
  nlinarith

/-- Every window of radius `≤ 693/2000` is closed. -/
theorem window_le_693_arithmetic_nonpositive {L : ℝ} (hL : L ≤ 693 / 2000) :
    WindowArithmeticNonpositiveV1 L :=
  windowArithmeticNonpositive_mono_v1 hL window_693_arithmetic_nonpositive

/-- The connected chain: RH follows from the sign on the windows above `693/2000`. -/
theorem rh_of_windows_above_693
    (h : ∀ L : ℝ, 693 / 2000 < L → WindowArithmeticNonpositiveV1 L) :
    RiemannHypothesis := by
  refine final_sign_implies_rh_v13 (fun g hm => ?_)
  obtain ⟨L, _, hw⟩ := logLift_has_finite_window_v1 g
  rcases le_or_gt L (693 / 2000) with hle | hlt
  · exact window_le_693_arithmetic_nonpositive hle g hm hw
  · exact h L hlt g hm hw

/-- Countable form: RH follows from the sign on the integer windows `[−n, n]`, `n ≥ 1`. -/
theorem rh_of_nat_windows
    (h : ∀ n : ℕ, 0 < n → WindowArithmeticNonpositiveV1 (n : ℝ)) :
    RiemannHypothesis :=
  rh_of_windows_above_693 (fun L _ g hm hw =>
    ((all_windows_iff_positive_nat_windows_v1).2 h) L
      (lt_of_lt_of_le (by norm_num) (le_of_lt ‹693 / 2000 < L›)) g hm hw)

end AEGIS.RHWindowConnectedV13

#print axioms AEGIS.RHWindowConnectedV13.window_693_arithmetic_nonpositive
#print axioms AEGIS.RHWindowConnectedV13.window_le_693_arithmetic_nonpositive
#print axioms AEGIS.RHWindowConnectedV13.rh_of_windows_above_693
#print axioms AEGIS.RHWindowConnectedV13.rh_of_nat_windows
