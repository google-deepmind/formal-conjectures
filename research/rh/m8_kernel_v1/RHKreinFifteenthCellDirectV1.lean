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

import RHKreinFifteenthCellReductionV1
import RHKreinFifteenthCellDirectCorrectionV1

/-!
# Fifteenth-cell premise-free soundness

Combines the derivative-free correction lower bound with the existing
fifteenth-cell symbol floor and weight bound.  The seven retained midpoint jet
premises of `RHKreinFifteenthCellReductionV1` are not needed.

No all-cells or RH statement is concluded.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFifteenthCellDirectV1

open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinFifteenthCellReductionV1
open AEGIS.RHKreinFourteenthCellCompositionV1
open AEGIS.RHKreinFifteenthCellDirectCorrectionV1

theorem fifteenthCell_sound_direct : CellAnalyticSoundV1 fifteenthCell := by
  apply cellAnalyticSound_of_correction_lower fifteenthCell (fun _ => directLower)
  · intro t hlo hhi
    norm_num [fifteenthCell] at hlo hhi
    exact correction_lower_direct t hlo hhi
  · intro t hlo hhi
    have hsym := fifteenthCell_symbol_lower t hlo hhi
    norm_num [fifteenthCell] at hlo hhi
    have ht0 : 0 ≤ t := by linarith
    have hw : (t ^ 2 + 1 / 4) ^ 2 ≤ fifteenthWeightUpper := by
      norm_num [fifteenthWeightUpper]
      nlinarith [sq_nonneg t,
        mul_nonneg (sub_nonneg.mpr hhi)
          (add_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 1275 / 16384))]
    have hw0 : 0 ≤ (t ^ 2 + 1 / 4) ^ 2 := sq_nonneg _
    have hlv : (lowerValue fifteenthCell : ℝ) = 292616690003685633 / 18446744073709551616 := by
      norm_num [fifteenthCell, lowerValue]
    have hground : fifteenthWeightUpper * (292616690003685633 / 18446744073709551616) ≤
        fifteenthWeightUpper * (fifteenthSymbolLower - 1 / 16) + directLower := by
      norm_num [fifteenthWeightUpper, fifteenthSymbolLower, directLower]
    have hneg : fifteenthSymbolLower - 1 / 16 ≤ 0 := by norm_num [fifteenthSymbolLower]
    rw [hlv]
    have h1 : (t ^ 2 + 1 / 4) ^ 2 * (292616690003685633 / 18446744073709551616 : ℝ) ≤
        fifteenthWeightUpper * (292616690003685633 / 18446744073709551616) :=
      mul_le_mul_of_nonneg_right hw (by norm_num)
    have h2 : fifteenthWeightUpper * (fifteenthSymbolLower - 1 / 16) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (fifteenthSymbolLower - 1 / 16) :=
      mul_le_mul_of_nonpos_right hw hneg
    have h3 : (t ^ 2 + 1 / 4) ^ 2 * (fifteenthSymbolLower - 1 / 16) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hsym _) hw0
    linarith

theorem first_fifteen_cells_sound :
    CellAnalyticSoundV1 AEGIS.RHKreinFirstCellV1.firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirdCellCompositionV1.thirdCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFourthCellCompositionV1.fourthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFifthCellCompositionV1.fifthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSixthCellReductionV1.sixthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSeventhCellCompositionV1.seventhCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinEighthCellCompositionV1.eighthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinNinthCellCompositionV1.ninthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinTenthCellCompositionV1.tenthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinEleventhCellCompositionV1.eleventhCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinTwelfthCellCompositionV1.twelfthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirteenthCellCompositionV1.thirteenthCell ∧
      CellAnalyticSoundV1 fourteenthCell ∧ CellAnalyticSoundV1 fifteenthCell :=
  ⟨first_fourteen_cells_sound.1, first_fourteen_cells_sound.2.1,
    first_fourteen_cells_sound.2.2.1, first_fourteen_cells_sound.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.2.2,
    fifteenthCell_sound_direct⟩

end AEGIS.RHKreinFifteenthCellDirectV1

#print axioms AEGIS.RHKreinFifteenthCellDirectV1.fifteenthCell_sound_direct
#print axioms AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound
