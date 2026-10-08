import RHNarrowMomentPacketV1
import RHFinalClosureSpineV1

/-!
AEGIS Ω — concrete narrow retained-sign composition v1.

This module instantiates the existing V3.1 actual arithmetic sign theorem on
the canonical nonzero moment-killed packet constructed in
RHNarrowMomentPacketV1.

It proves a concrete, coefficient-uniform three-block sign theorem for the
actual repository Weil RHS.  It is not the universal Bombieri criterion.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowRetainedSignV1

open AEGIS.RHNarrowMomentPacketV1
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedAlgebraV2

/-- Full V3.1 coercive estimate instantiated on the canonical narrow packet. -/
theorem narrow_three_block_coercive_v1
    (z0 z1 z2 : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (combo z0 z1 z2
          (gMinus gNarrow) (gZero gNarrow) (gPlus gNarrow)))).re ≤
      -(1 / 10 : ℝ) *
        AEGIS.WeilDisjointEnergyV2.energy
          (combo z0 z1 z2
            (gMinus gNarrow) (gZero gNarrow) (gPlus gNarrow)).1 := by
  exact
    AEGIS.WeilSeparatedArchBridgeV31.three_block_bound_of_moments
      gNarrow 0 gNarrow_width gNarrow_moments z0 z1 z2

/-- Sign-only form of the same concrete theorem. -/
theorem narrow_three_block_sign_v1
    (z0 z1 z2 : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (combo z0 z1 z2
          (gMinus gNarrow) (gZero gNarrow) (gPlus gNarrow)))).re ≤ 0 := by
  exact
    AEGIS.RHFinalClosureV1.retained_three_block_sign_v1
      gNarrow 0 gNarrow_width gNarrow_moments z0 z1 z2

end AEGIS.RHNarrowRetainedSignV1

#print axioms AEGIS.RHNarrowRetainedSignV1.narrow_three_block_coercive_v1
#print axioms AEGIS.RHNarrowRetainedSignV1.narrow_three_block_sign_v1
