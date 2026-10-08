import Mathlib.Tactic

/-!
AEGIS Ω — four-block absolute-budget obstruction v1.

This is a proof-method obstruction, not an RH statement.

The retained V3.1 certificate uses:
- diagonal coercivity 103/100 per packet;
- adjacent absolute cross bound 51/100;
- next-neighbour absolute cross bound 9/25.

For four consecutive dyadic packets, even if the farthest cross term is
discarded entirely, the scalar absolute-value aggregation already loses:

  4*(103/100) < 2*(3*(51/100) + 2*(9/25)).

Hence the three-block Gershgorin/absolute-cross argument cannot be iterated
to four blocks without using additional signed/exact structure.

AUTHORITY_EFFECT = NONE
RH = NOT_PROVEN
-/

set_option autoImplicit false

namespace AEGIS.RHFourBlockBoundObstructionV1

theorem four_block_absolute_budget_fails_v1 :
    4 * ((103 : ℝ) / 100) <
      2 * (3 * ((51 : ℝ) / 100) + 2 * ((9 : ℝ) / 25)) := by
  norm_num

theorem four_block_missing_margin_v1 :
    2 * (3 * ((51 : ℝ) / 100) + 2 * ((9 : ℝ) / 25)) -
      4 * ((103 : ℝ) / 100) = (19 : ℝ) / 50 := by
  norm_num

end AEGIS.RHFourBlockBoundObstructionV1

#print axioms AEGIS.RHFourBlockBoundObstructionV1.four_block_absolute_budget_fails_v1
#print axioms AEGIS.RHFourBlockBoundObstructionV1.four_block_missing_margin_v1
