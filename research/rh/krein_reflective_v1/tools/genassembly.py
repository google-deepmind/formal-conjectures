import json
B=json.load(open('/home/user/mathlib4-433/tree_cell2/batches.json'))
n=len(B)
imports="\n".join(f"import {nm}" for nm,s,m in B)
cases="\n".join(
  f"  · rw [chunk_eq]; " + (f"exact batch{s:04d}" if m==10 else f"rw [show slice {s} 10 = slice {s} {m} by decide +kernel]; exact batch{s:04d}")
  for nm,s,m in B)
txt=f"""/-
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

import RHKreinFifteenthCellDirectV1
{imports}

/-!
# All 2199 cells of the order-19 L = 4/5 Krein certificate

Cells 0–14: the existing kernel closures (`first_fifteen_cells_sound`).
Cells 15–2198: the reflective checker, {n} batch modules, `decide +kernel`.

Consequently `PointwiseCertificate` holds and the actual zero quadratic has margin `E/16` on every
moment-zero packet of logarithmic half-width at most `2/5`.  A fixed support width; not RH.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinAllCellsV1

open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinCellBatchV1

theorem first_fifteen : ∀ c ∈ finiteCells.take 15, CellAnalyticSoundV1 c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound
  have e : finiteCells.take 15 = [AEGIS.RHKreinFirstCellV1.firstCell,
      AEGIS.RHKreinSecondCellReductionV1.secondCell, AEGIS.RHKreinThirdCellCompositionV1.thirdCell,
      AEGIS.RHKreinFourthCellCompositionV1.fourthCell, AEGIS.RHKreinFifthCellCompositionV1.fifthCell,
      AEGIS.RHKreinSixthCellReductionV1.sixthCell, AEGIS.RHKreinSeventhCellCompositionV1.seventhCell,
      AEGIS.RHKreinEighthCellCompositionV1.eighthCell, AEGIS.RHKreinNinthCellCompositionV1.ninthCell,
      AEGIS.RHKreinTenthCellCompositionV1.tenthCell, AEGIS.RHKreinEleventhCellCompositionV1.eleventhCell,
      AEGIS.RHKreinTwelfthCellCompositionV1.twelfthCell,
      AEGIS.RHKreinThirteenthCellCompositionV1.thirteenthCell,
      AEGIS.RHKreinFourteenthCellCompositionV1.fourteenthCell,
      AEGIS.RHKreinFifteenthCellReductionV1.fifteenthCell] := by decide +kernel
  rw [e]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals assumption

theorem mem_of_chunks {{α : Type}} (P : α → Prop) (size : ℕ) :
    ∀ (n : ℕ) (L : List α), (∀ k < n, ∀ c ∈ (L.drop (size * k)).take size, P c) →
      L.length ≤ size * n → ∀ c ∈ L, P c
  | 0, L, _, hlen => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this; simp
  | n + 1, L, h, hlen => by
    intro c hc
    rw [← List.take_append_drop size L] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h 0 (Nat.succ_pos n) c (by simpa using hc)
    · refine mem_of_chunks P size n (L.drop size) ?_ ?_ c hc
      · intro k hk x hx
        refine h (k + 1) (by omega) x ?_
        rwa [List.drop_drop, show size + size * k = size * (k + 1) by ring] at hx
      · simp only [List.length_drop]; rw [Nat.mul_succ] at hlen; omega

theorem chunk_eq (k : ℕ) :
    ((finiteCells.drop 15).drop (10 * k)).take 10 = slice (15 + 10 * k) 10 := by
  simp only [slice, List.drop_drop]

theorem remaining : ∀ c ∈ finiteCells.drop 15, CellAnalyticSoundV1 c := by
  refine mem_of_chunks (fun c => CellAnalyticSoundV1 c) 10 {n} (finiteCells.drop 15) ?_ ?_
  intro k hk
  interval_cases k
{cases}
  · decide +kernel

theorem allCellsAnalyticSound : AllCellsAnalyticSoundV1 := by
  intro c hc
  rw [← List.take_append_drop 15 finiteCells] at hc
  rcases List.mem_append.mp hc with h | h
  · exact first_fifteen c h
  · exact remaining c h

theorem pointwiseCertificate : AEGIS.RHKreinExplicitCorrectionV1.PointwiseCertificate :=
  pointwiseCertificate_of_allCellsAnalyticSound_v1 allCellsAnalyticSound

/-- The actual zero quadratic of every moment-zero packet of logarithmic half-width at most
`2/5` dominates one sixteenth of its energy. -/
theorem zero_quadratic_margin_two_fifths
    (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (1 / 16) * AEGIS.WeilDisjointEnergyV2.energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  actual_zero_quadratic_margin_of_allCellsAnalyticSound_v1 allCellsAnalyticSound g r a hr0 hr hw hm

end AEGIS.RHKreinAllCellsV1

#print axioms AEGIS.RHKreinAllCellsV1.allCellsAnalyticSound
#print axioms AEGIS.RHKreinAllCellsV1.zero_quadratic_margin_two_fifths
"""
open('/home/user/mathlib4-433/tree_cell2/RHKreinAllCellsV1.lean','w').write(txt)
print('written', n)
