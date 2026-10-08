import RHThreeCellClassV13
import WeilWindowExhaustionV1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHWindowSevenOver32V1
open AEGIS.RHThreeCellClassV13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilWindowExhaustionV1

theorem window_seven_over_32_arithmetic_nonpositive_v1 :
    WindowArithmeticNonpositiveV1 (7 / 32) := by
  intro g hm hwindow
  have hw : HalfWidthAt g (7 / 32) 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  have hc := cell_coercive g 0 hw hm
  have hE := energy_nonnegative g.1
  linarith

theorem window_le_seven_over_32_arithmetic_nonpositive_v1
    {L : ℝ} (hL : L ≤ 7 / 32) : WindowArithmeticNonpositiveV1 L :=
  windowArithmeticNonpositive_mono_v1 hL
    window_seven_over_32_arithmetic_nonpositive_v1

end AEGIS.RHWindowSevenOver32V1

#print axioms AEGIS.RHWindowSevenOver32V1.window_seven_over_32_arithmetic_nonpositive_v1
#print axioms AEGIS.RHWindowSevenOver32V1.window_le_seven_over_32_arithmetic_nonpositive_v1
