/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import RHKreinL105Batch000
import RHKreinL105Batch001
import RHKreinL105Batch002
import RHKreinL105Batch003
import RHKreinL105Batch004
import RHKreinL105Batch005
import RHKreinL105Batch006
import RHKreinL105Batch007
import RHKreinL105Batch008
import RHKreinL105Batch009
import RHKreinL105Batch010
import RHKreinL105Batch011
import RHKreinL105Batch012
import RHKreinL105Batch013
import RHKreinL105Batch014
import RHKreinL105Batch015
import RHKreinL105Batch016
import RHKreinL105Batch017
import RHKreinL105Batch018
import RHKreinL105Batch019
import RHKreinL105Batch020
import RHKreinL105Batch021
import RHKreinL105Batch022
import RHKreinL105Batch023
import RHKreinL105Batch024
import RHKreinL105Batch025
import RHKreinL105Batch026
import RHKreinL105Batch027
import RHKreinL105Batch028
import RHKreinL105Batch029
import RHKreinL105Batch030
import RHKreinL105Batch031
import RHKreinL105Batch032
import RHKreinL105Batch033
import RHKreinL105Batch034
import RHKreinL105Batch035
import RHKreinL105Batch036
import RHKreinL105Batch037
import RHKreinL105Batch038
import RHKreinL105Batch039
import RHKreinL105Batch040
import RHKreinL105Batch041
import RHKreinL105Batch042
import RHKreinL105Batch043
import RHKreinL105Batch044
import RHKreinL105Batch045
import RHKreinL105Batch046
import RHKreinL105Batch047
import RHKreinL105Batch048
import RHKreinL105Batch049
import RHKreinL105Batch050
import RHKreinL105Batch051
import RHKreinL105Batch052
import RHKreinL105Batch053
import RHKreinL105Batch054
import RHKreinL105Batch055
import RHKreinL105Batch056
import RHKreinL105Batch057
import RHKreinL105Batch058
import RHKreinL105Batch059
import RHKreinL105Batch060
import RHKreinL105Batch061
import RHKreinL105Batch062
import RHKreinL105Batch063
import RHKreinL105Batch064
import RHKreinL105Batch065
import RHKreinL105Batch066
import RHKreinL105Batch067
import RHKreinL105Batch068
import RHKreinL105Batch069
import RHKreinL105Batch070
import RHKreinL105Batch071
import RHKreinL105Batch072
import RHKreinL105Batch073
import RHKreinL105Batch074
import RHKreinL105Batch075
import RHKreinL105Batch076
import RHKreinL105Batch077
import RHKreinL105Batch078
import RHKreinL105Batch079
import RHKreinL105Batch080
import RHKreinL105Batch081
import RHKreinL105Batch082
import RHKreinL105Batch083
import RHKreinL105Batch084
import RHKreinL105Batch085
import RHKreinL105Batch086
import RHKreinL105Batch087
import RHKreinL105Batch088
import RHKreinL105Batch089
import RHKreinL105Batch090
import RHKreinL105Batch091
import RHKreinL105Batch092
import RHKreinL105Batch093
import RHKreinL105Batch094
import RHKreinL105Batch095
import RHKreinL105Batch096
import RHKreinL105Batch097
import RHKreinL105Batch098
import RHKreinL105Batch099
import RHKreinL105Batch100
import RHKreinL105Batch101
import RHKreinL105Batch102
import RHKreinL105Batch103
import RHKreinL105Batch104
import RHKreinL105Batch105
import RHKreinL105Batch106
import RHKreinL105Batch107
import RHKreinL105Batch108
import RHKreinL105Batch109
import RHKreinL105Batch110
import RHKreinL105Batch111
import RHKreinL105Batch112
import RHKreinL105Batch113
import RHKreinL105Batch114
import RHKreinL105Batch115
import RHKreinL105BridgeV1

/-!
# The `L = 21/20` Krein certificate, assembled

116 batch modules of kernel-checked wide cells cover `[0, 3000]`; the tail `t ≥ 3000` is one
`decide`; evenness covers `t < 0`.  The bridge turns this into nonnegativity of the actual zeta zero
quadratic on every moment-zero packet with `2r < 21/20`.  A fixed support width; not RH.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinL105AllV1
open AEGIS.RHKreinL105CheckerV1 AEGIS.RHKreinL105TailV1 AEGIS.RHKreinL105BatchV1
open AEGIS.RHKreinL105BridgeV1

theorem fcert_finite : ∀ t : ℝ, (((0 : ℚ)) : ℝ) ≤ t → t ≤ (((3000 : ℚ)) : ℝ) → 0 ≤ Fcert t :=
  (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue (glue b000 b001) b002) b003) b004) b005) b006) b007) b008) b009) b010) b011) b012) b013) b014) b015) b016) b017) b018) b019) b020) b021) b022) b023) b024) b025) b026) b027) b028) b029) b030) b031) b032) b033) b034) b035) b036) b037) b038) b039) b040) b041) b042) b043) b044) b045) b046) b047) b048) b049) b050) b051) b052) b053) b054) b055) b056) b057) b058) b059) b060) b061) b062) b063) b064) b065) b066) b067) b068) b069) b070) b071) b072) b073) b074) b075) b076) b077) b078) b079) b080) b081) b082) b083) b084) b085) b086) b087) b088) b089) b090) b091) b092) b093) b094) b095) b096) b097) b098) b099) b100) b101) b102) b103) b104) b105) b106) b107) b108) b109) b110) b111) b112) b113) b114) b115)

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
