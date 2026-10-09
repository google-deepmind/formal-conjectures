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

import RHKreinCellCheckerV1

/-!
# Batches of serialized cells

`checkAll pa cells breaks` runs `checkCell` along two aligned lists.  Batch modules discharge
`checkAll pa (slice k) (breaks k) = true` by `decide +kernel`; `checkAll_sound` turns each into
analytic soundness of every cell of the slice.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

/-- The checker parameters used for the whole order-19 certificate. -/
def pa19 : Params := ⟨⟨14, 30, 11, 120⟩, 10, 120, 16⟩

def checkAll (pa : Params) : List FiniteCellV1 → List (List ℚ) → Bool
  | [], [] => true
  | c :: cs, b :: bs => checkCell pa c b && checkAll pa cs bs
  | _, _ => false

theorem checkAll_sound (pa : Params) :
    ∀ (cs : List FiniteCellV1) (bs : List (List ℚ)), checkAll pa cs bs = true →
      ∀ c ∈ cs, CellAnalyticSoundV1 c
  | [], _, _ => by simp
  | c :: cs, [], h => by simp [checkAll] at h
  | c :: cs, b :: bs, h => by
    simp only [checkAll, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact checkCell_sound pa x b h.1
    · exact checkAll_sound pa cs bs h.2 x hx

/-- The `i`-th serialized cell. -/
def cellAt (i : ℕ) : FiniteCellV1 := finiteCells.getD i ⟨0, 0, 0⟩

/-- The `k`-th slice of the serialized cells after the first fifteen. -/
def slice (start len : ℕ) : List FiniteCellV1 := (finiteCells.drop start).take len

end AEGIS.RHKreinCellBatchV1
