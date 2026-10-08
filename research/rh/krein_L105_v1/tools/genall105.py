import json
from pathlib import Path
from fractions import Fraction as Q
R=str(Path(__file__).resolve().parents[1])
B=json.loads((Path(__file__).resolve().parent / 'batches105.json').read_text(encoding='utf-8'))
HDR=(Path(R)/'RHKreinHatAtV1.lean').read_text().split('-/')[0]+'-/\n'
if not B or any(name != f'RHKreinL105Batch{i:03d}' or not indices for i,(name,indices) in enumerate(B)):
    raise ValueError('L105_INVALID_BATCH_MANIFEST')
imports="\n".join(f"import {nm}" for nm,_ in B)
e=f"b{0:03d}"
for k in range(1,len(B)): e=f"(glue {e} b{k:03d})"
s=HDR+f"""
{imports}
import RHKreinL105BridgeV1

/-!
# The `L = 21/20` Krein certificate, assembled

{len(B)} batch modules of kernel-checked wide cells cover `[0, 3000]`; the tail `t ≥ 3000` is one
`decide`; evenness covers `t < 0`.  The bridge turns this into nonnegativity of the actual zeta zero
quadratic on every moment-zero packet with `2r < 21/20`.  A fixed support width; not RH.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinL105AllV1
open AEGIS.RHKreinL105CheckerV1 AEGIS.RHKreinL105TailV1 AEGIS.RHKreinL105BatchV1
open AEGIS.RHKreinL105BridgeV1

theorem fcert_finite : ∀ t : ℝ, (((0 : ℚ)) : ℝ) ≤ t → t ≤ (((3000 : ℚ)) : ℝ) → 0 ≤ Fcert t :=
  {e}

theorem tail_check : tailCheck 120 256 3000 = true := by decide +kernel

theorem zero_quadratic_nonneg_width_21_20
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < 21 / 20) (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  zero_quadratic_nonneg_L105 (fun t h0 h1 => fcert_finite t (by simpa using h0) (by simpa using h1))
    120 256 tail_check g hmom r a hr hrL hw

end AEGIS.RHKreinL105AllV1

#print axioms AEGIS.RHKreinL105AllV1.zero_quadratic_nonneg_width_21_20
"""
open(f'{R}/RHKreinL105AllV1.lean','w').write(s); print('written', len(B))
