import RHHatCellsV13

/-!
AEGIS Ω — Weil positivity on the half-width-1/3 class via a positive-definite kernel, V13.

Certificate for `RHHatBudgetV13.hat_diagonal`: `h = 1/72`, `n = 289` integer weights `vCert` (a
minimum-phase spectral factor, scaled by `10³`, of an LP-optimal positive-definite sequence;
`ρ_k` are checked by kernel evaluation of integer sums), `σ = 10⁻⁶`,
`λ = 833/400`, cap boundaries `t₁ = 2/9`, `t₂ = 1/3`.  The kernel condition holds on
`(0, 2/3]` by `Q_of_checks` (192 sub-cells), the kernel integrals are exact trapezoid sums of
the autocorrelation values `ρ_k`, and `hatGain(1/3) ≤ −1/100`.
Every moment-zero packet of log-half-width `≤ 1/3` (support `≤ 2/3`) has `Re RHS ≤ −E/100`
and a nonnegative canonical zero quadratic.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatClass13V13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13
open AEGIS.RHHatCellsV13

/-- The integer weights, as a list. -/
def wL : List ℤ :=
  [39751, -12143, -6868, -2775, -5403, -2801, -981, -3669, -120, 369, 43, -4101,
   302, 2502, -4953, 4267, 550, -1415, 2783, 170, 1449, -278, 1805, 665,
   -202, 1243, 188, 954, -727, 1077, 422, -1075, 383, 632, -1265, -95,
   917, -2223, 1204, -321, -151, 864, -1665, -1524, 335, -1189, -2469, -538,
   -4411, -49812, 35546, 15986, 9645, 6137, 1797, 1608, 1756, -3198, -1017, -700,
   538, -792, -4329, 1561, -4167, -1873, -835, -1492, -1346, -1806, 1418, -2129,
   316, 140, 618, -481, -210, 2621, -1737, 1396, 1145, 540, 412, 204,
   2560, -1310, 1512, 894, -545, 12, 797, 2323, 225, 524, 2340, -167,
   2027, 5710, 38313, -53156, -19198, -11005, 4977, 2339, 1488, 4744, 7394, 1108,
   2183, 5557, -1905, 4885, 2522, -1416, 3482, 6, -1725, 2263, -1799, -468,
   -361, -2405, 1798, -4263, 709, 286, -3373, 807, -1527, 983, -4279, 2160,
   1912, -7582, 6306, -916, -4575, 5156, -469, -2514, 49, 2464, -2261, -772,
   4988, -5029, -1572, -19792, 51889, 13187, 1398, -19482, -4734, -5778, -7614, -7445,
   932, -1099, -7705, 7431, -3237, -2570, 7029, -4070, 3735, 1216, -711, 5373,
   -4349, 5123, 2131, -5400, 7491, -1651, -2221, 3488, 722, -1779, -2146, 7888,
   -8243, -1116, 10549, -12998, 3581, 5323, -9226, 2516, 2675, -2045, -3176, 3611,
   -1262, -5831, 7335, -2880, 8154, -35113, -2510, 9826, 21861, 2204, 5589, 2690,
   3611, -3920, -2224, 5817, -10246, 1050, 1118, -6815, 2837, -4676, 2605, -2278,
   -4043, 8083, -8301, 1125, 6669, -8379, 3183, 3621, -3461, -923, 4719, 750,
   -7656, 11173, -2434, -8108, 13851, -7155, -2321, 7574, -4421, -1773, 1132, 2103,
   -2483, 1172, 2757, -5063, 3151, -3309, 14840, -3453, -9403, -10380, 1271, -1295,
   2244, -771, 4011, 2838, -3404, 6592, -565, -782, 2467, -1096, 1810, -3603,
   3053, 312, -5581, 6081, -2769, -3693, 5319, -2962, -2062, 2383, 64, -3088,
   625, 3960, -6609, 3074, 3653, -7340, 5818, -161, -2329, 2917, 932, 524,
   -2526]

/-- The weights as a real sequence. -/
def vCert (i : ℕ) : ℝ := ((wL.getD i 0 : ℤ) : ℝ)

/-- `ρ_k` of the real weights is the cast of an integer sum. -/
theorem rhoZ (k : ℕ) : rhoK 289 vCert k =
    ((∑ j ∈ Finset.range 289, if j + k < 289 then wL.getD (j + k) 0 * wL.getD j 0 else 0 : ℤ) : ℝ) := by
  unfold rhoK vCert; push_cast; rfl

/-- The autocorrelation values `ρ_0 … ρ_48`. -/
def rv : ℕ → ℝ
  | 0 => 20467196598
  | 1 => -3449853364
  | 2 => -1943997462
  | 3 => -1295360652
  | 4 => -938258702
  | 5 => -713112928
  | 6 => -558312067
  | 7 => -445628901
  | 8 => -359912480
  | 9 => -292427979
  | 10 => -238004617
  | 11 => -193076419
  | 12 => -155413217
  | 13 => -123322547
  | 14 => -95729917
  | 15 => -71802876
  | 16 => -50594839
  | 17 => -31855666
  | 18 => -14995920
  | 19 => -31258
  | 20 => 13653401
  | 21 => 26178500
  | 22 => 37408238
  | 23 => 47717693
  | 24 => 57457808
  | 25 => 66175179
  | 26 => 74679869
  | 27 => 82240627
  | 28 => 89381448
  | 29 => 96314545
  | 30 => 102705712
  | 31 => 108625591
  | 32 => 114420382
  | 33 => 119775938
  | 34 => 124973394
  | 35 => 129775766
  | 36 => 134428220
  | 37 => 138978744
  | 38 => 143322360
  | 39 => 147415681
  | 40 => 151366961
  | 41 => 155238017
  | 42 => 158795432
  | 43 => 162431613
  | 44 => 165961681
  | 45 => 169298371
  | 46 => 172540250
  | 47 => 175852937
  | 48 => 178718737
  | _ => 0

/-- `λ`. -/
def lamC : ℝ := ((833 : ℝ) / 400)

/-- `σ = 10⁻⁶`. -/
def sigC : ℝ := 1 / 1000000

set_option maxRecDepth 100000 in
theorem rho_0 : rhoK 289 vCert 0 = 20467196598 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 0 < 289 then wL.getD (j + 0) 0 * wL.getD j 0 else 0 : ℤ) = 20467196598)

set_option maxRecDepth 100000 in
theorem rho_1 : rhoK 289 vCert 1 = -3449853364 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 1 < 289 then wL.getD (j + 1) 0 * wL.getD j 0 else 0 : ℤ) = -3449853364)

set_option maxRecDepth 100000 in
theorem rho_2 : rhoK 289 vCert 2 = -1943997462 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 2 < 289 then wL.getD (j + 2) 0 * wL.getD j 0 else 0 : ℤ) = -1943997462)

set_option maxRecDepth 100000 in
theorem rho_3 : rhoK 289 vCert 3 = -1295360652 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 3 < 289 then wL.getD (j + 3) 0 * wL.getD j 0 else 0 : ℤ) = -1295360652)

set_option maxRecDepth 100000 in
theorem rho_4 : rhoK 289 vCert 4 = -938258702 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 4 < 289 then wL.getD (j + 4) 0 * wL.getD j 0 else 0 : ℤ) = -938258702)

set_option maxRecDepth 100000 in
theorem rho_5 : rhoK 289 vCert 5 = -713112928 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 5 < 289 then wL.getD (j + 5) 0 * wL.getD j 0 else 0 : ℤ) = -713112928)

set_option maxRecDepth 100000 in
theorem rho_6 : rhoK 289 vCert 6 = -558312067 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 6 < 289 then wL.getD (j + 6) 0 * wL.getD j 0 else 0 : ℤ) = -558312067)

set_option maxRecDepth 100000 in
theorem rho_7 : rhoK 289 vCert 7 = -445628901 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 7 < 289 then wL.getD (j + 7) 0 * wL.getD j 0 else 0 : ℤ) = -445628901)

set_option maxRecDepth 100000 in
theorem rho_8 : rhoK 289 vCert 8 = -359912480 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 8 < 289 then wL.getD (j + 8) 0 * wL.getD j 0 else 0 : ℤ) = -359912480)

set_option maxRecDepth 100000 in
theorem rho_9 : rhoK 289 vCert 9 = -292427979 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 9 < 289 then wL.getD (j + 9) 0 * wL.getD j 0 else 0 : ℤ) = -292427979)

set_option maxRecDepth 100000 in
theorem rho_10 : rhoK 289 vCert 10 = -238004617 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 10 < 289 then wL.getD (j + 10) 0 * wL.getD j 0 else 0 : ℤ) = -238004617)

set_option maxRecDepth 100000 in
theorem rho_11 : rhoK 289 vCert 11 = -193076419 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 11 < 289 then wL.getD (j + 11) 0 * wL.getD j 0 else 0 : ℤ) = -193076419)

set_option maxRecDepth 100000 in
theorem rho_12 : rhoK 289 vCert 12 = -155413217 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 12 < 289 then wL.getD (j + 12) 0 * wL.getD j 0 else 0 : ℤ) = -155413217)

set_option maxRecDepth 100000 in
theorem rho_13 : rhoK 289 vCert 13 = -123322547 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 13 < 289 then wL.getD (j + 13) 0 * wL.getD j 0 else 0 : ℤ) = -123322547)

set_option maxRecDepth 100000 in
theorem rho_14 : rhoK 289 vCert 14 = -95729917 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 14 < 289 then wL.getD (j + 14) 0 * wL.getD j 0 else 0 : ℤ) = -95729917)

set_option maxRecDepth 100000 in
theorem rho_15 : rhoK 289 vCert 15 = -71802876 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 15 < 289 then wL.getD (j + 15) 0 * wL.getD j 0 else 0 : ℤ) = -71802876)

set_option maxRecDepth 100000 in
theorem rho_16 : rhoK 289 vCert 16 = -50594839 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 16 < 289 then wL.getD (j + 16) 0 * wL.getD j 0 else 0 : ℤ) = -50594839)

set_option maxRecDepth 100000 in
theorem rho_17 : rhoK 289 vCert 17 = -31855666 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 17 < 289 then wL.getD (j + 17) 0 * wL.getD j 0 else 0 : ℤ) = -31855666)

set_option maxRecDepth 100000 in
theorem rho_18 : rhoK 289 vCert 18 = -14995920 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 18 < 289 then wL.getD (j + 18) 0 * wL.getD j 0 else 0 : ℤ) = -14995920)

set_option maxRecDepth 100000 in
theorem rho_19 : rhoK 289 vCert 19 = -31258 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 19 < 289 then wL.getD (j + 19) 0 * wL.getD j 0 else 0 : ℤ) = -31258)

set_option maxRecDepth 100000 in
theorem rho_20 : rhoK 289 vCert 20 = 13653401 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 20 < 289 then wL.getD (j + 20) 0 * wL.getD j 0 else 0 : ℤ) = 13653401)

set_option maxRecDepth 100000 in
theorem rho_21 : rhoK 289 vCert 21 = 26178500 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 21 < 289 then wL.getD (j + 21) 0 * wL.getD j 0 else 0 : ℤ) = 26178500)

set_option maxRecDepth 100000 in
theorem rho_22 : rhoK 289 vCert 22 = 37408238 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 22 < 289 then wL.getD (j + 22) 0 * wL.getD j 0 else 0 : ℤ) = 37408238)

set_option maxRecDepth 100000 in
theorem rho_23 : rhoK 289 vCert 23 = 47717693 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 23 < 289 then wL.getD (j + 23) 0 * wL.getD j 0 else 0 : ℤ) = 47717693)

set_option maxRecDepth 100000 in
theorem rho_24 : rhoK 289 vCert 24 = 57457808 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 24 < 289 then wL.getD (j + 24) 0 * wL.getD j 0 else 0 : ℤ) = 57457808)

set_option maxRecDepth 100000 in
theorem rho_25 : rhoK 289 vCert 25 = 66175179 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 25 < 289 then wL.getD (j + 25) 0 * wL.getD j 0 else 0 : ℤ) = 66175179)

set_option maxRecDepth 100000 in
theorem rho_26 : rhoK 289 vCert 26 = 74679869 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 26 < 289 then wL.getD (j + 26) 0 * wL.getD j 0 else 0 : ℤ) = 74679869)

set_option maxRecDepth 100000 in
theorem rho_27 : rhoK 289 vCert 27 = 82240627 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 27 < 289 then wL.getD (j + 27) 0 * wL.getD j 0 else 0 : ℤ) = 82240627)

set_option maxRecDepth 100000 in
theorem rho_28 : rhoK 289 vCert 28 = 89381448 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 28 < 289 then wL.getD (j + 28) 0 * wL.getD j 0 else 0 : ℤ) = 89381448)

set_option maxRecDepth 100000 in
theorem rho_29 : rhoK 289 vCert 29 = 96314545 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 29 < 289 then wL.getD (j + 29) 0 * wL.getD j 0 else 0 : ℤ) = 96314545)

set_option maxRecDepth 100000 in
theorem rho_30 : rhoK 289 vCert 30 = 102705712 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 30 < 289 then wL.getD (j + 30) 0 * wL.getD j 0 else 0 : ℤ) = 102705712)

set_option maxRecDepth 100000 in
theorem rho_31 : rhoK 289 vCert 31 = 108625591 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 31 < 289 then wL.getD (j + 31) 0 * wL.getD j 0 else 0 : ℤ) = 108625591)

set_option maxRecDepth 100000 in
theorem rho_32 : rhoK 289 vCert 32 = 114420382 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 32 < 289 then wL.getD (j + 32) 0 * wL.getD j 0 else 0 : ℤ) = 114420382)

set_option maxRecDepth 100000 in
theorem rho_33 : rhoK 289 vCert 33 = 119775938 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 33 < 289 then wL.getD (j + 33) 0 * wL.getD j 0 else 0 : ℤ) = 119775938)

set_option maxRecDepth 100000 in
theorem rho_34 : rhoK 289 vCert 34 = 124973394 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 34 < 289 then wL.getD (j + 34) 0 * wL.getD j 0 else 0 : ℤ) = 124973394)

set_option maxRecDepth 100000 in
theorem rho_35 : rhoK 289 vCert 35 = 129775766 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 35 < 289 then wL.getD (j + 35) 0 * wL.getD j 0 else 0 : ℤ) = 129775766)

set_option maxRecDepth 100000 in
theorem rho_36 : rhoK 289 vCert 36 = 134428220 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 36 < 289 then wL.getD (j + 36) 0 * wL.getD j 0 else 0 : ℤ) = 134428220)

set_option maxRecDepth 100000 in
theorem rho_37 : rhoK 289 vCert 37 = 138978744 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 37 < 289 then wL.getD (j + 37) 0 * wL.getD j 0 else 0 : ℤ) = 138978744)

set_option maxRecDepth 100000 in
theorem rho_38 : rhoK 289 vCert 38 = 143322360 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 38 < 289 then wL.getD (j + 38) 0 * wL.getD j 0 else 0 : ℤ) = 143322360)

set_option maxRecDepth 100000 in
theorem rho_39 : rhoK 289 vCert 39 = 147415681 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 39 < 289 then wL.getD (j + 39) 0 * wL.getD j 0 else 0 : ℤ) = 147415681)

set_option maxRecDepth 100000 in
theorem rho_40 : rhoK 289 vCert 40 = 151366961 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 40 < 289 then wL.getD (j + 40) 0 * wL.getD j 0 else 0 : ℤ) = 151366961)

set_option maxRecDepth 100000 in
theorem rho_41 : rhoK 289 vCert 41 = 155238017 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 41 < 289 then wL.getD (j + 41) 0 * wL.getD j 0 else 0 : ℤ) = 155238017)

set_option maxRecDepth 100000 in
theorem rho_42 : rhoK 289 vCert 42 = 158795432 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 42 < 289 then wL.getD (j + 42) 0 * wL.getD j 0 else 0 : ℤ) = 158795432)

set_option maxRecDepth 100000 in
theorem rho_43 : rhoK 289 vCert 43 = 162431613 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 43 < 289 then wL.getD (j + 43) 0 * wL.getD j 0 else 0 : ℤ) = 162431613)

set_option maxRecDepth 100000 in
theorem rho_44 : rhoK 289 vCert 44 = 165961681 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 44 < 289 then wL.getD (j + 44) 0 * wL.getD j 0 else 0 : ℤ) = 165961681)

set_option maxRecDepth 100000 in
theorem rho_45 : rhoK 289 vCert 45 = 169298371 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 45 < 289 then wL.getD (j + 45) 0 * wL.getD j 0 else 0 : ℤ) = 169298371)

set_option maxRecDepth 100000 in
theorem rho_46 : rhoK 289 vCert 46 = 172540250 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 46 < 289 then wL.getD (j + 46) 0 * wL.getD j 0 else 0 : ℤ) = 172540250)

set_option maxRecDepth 100000 in
theorem rho_47 : rhoK 289 vCert 47 = 175852937 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 47 < 289 then wL.getD (j + 47) 0 * wL.getD j 0 else 0 : ℤ) = 175852937)

set_option maxRecDepth 100000 in
theorem rho_48 : rhoK 289 vCert 48 = 178718737 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 289,
    if j + 48 < 289 then wL.getD (j + 48) 0 * wL.getD j 0 else 0 : ℤ) = 178718737)

theorem nodeV (k : ℕ) (hk : k ≤ 48) : hatK (1 / 72) 289 vCert ((k : ℝ) * (1 / 72)) = (1 / 72) * rv k := by
  rw [hatK_node _ (by norm_num)]
  interval_cases k <;> norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rv]

set_option maxHeartbeats 20000000 in
theorem checks_0 : ∀ m : ℕ, m < 48 → 0 ≤ checkF lamC sigC ((1 / 72) * rv (m / 4))
    ((1 / 72) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (1 / 72)) := by
  intro m hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_1 : ∀ m : ℕ, 48 ≤ m → m < 96 → 0 ≤ checkF lamC sigC ((1 / 72) * rv (m / 4))
    ((1 / 72) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (1 / 72)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_2 : ∀ m : ℕ, 96 ≤ m → m < 144 → 0 ≤ checkF lamC sigC ((1 / 72) * rv (m / 4))
    ((1 / 72) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (1 / 72)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_3 : ∀ m : ℕ, 144 ≤ m → m < 192 → 0 ≤ checkF lamC sigC ((1 / 72) * rv (m / 4))
    ((1 / 72) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (1 / 72)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

theorem Q_all : ∀ u ∈ Ioc (0 : ℝ) (2 * (1 / 3)), 0 ≤ kernelQ lamC sigC (1 / 72) 289 vCert u := by
  have e : (2 : ℝ) * (1 / 3) = ((48 : ℕ) : ℝ) * (1 / 72) := by norm_num
  rw [e]
  apply Q_of_checks lamC sigC (1 / 72) 289 vCert 48 4 rv (by norm_num) (by norm_num [sigC])
    (by norm_num [lamC]) (by norm_num) (by norm_num) nodeV
  intro m hm
  by_cases h0 : m < 48
  · exact checks_0 m h0
  push Not at h0
  by_cases h1 : m < 96
  · exact checks_1 m (by omega) h1
  push Not at h1
  by_cases h2 : m < 144
  · exact checks_2 m (by omega) h2
  push Not at h2
  exact checks_3 m (by omega) (by omega)

theorem int_1 : (∫ u in Ioc (0 : ℝ) ((2 : ℝ) / 9), hatK (1 / 72) 289 vCert u) = ((-1331826497 : ℝ) / 10368) := by
  have h := hatK_run_integral (1 / 72) (by norm_num) 289 vCert 0 16
  rw [show (((0 : ℕ) : ℝ)) * (1 / 72) = (0 : ℝ) by norm_num,
    show (((0 + 16 : ℕ) : ℝ)) * (1 / 72) = ((2 : ℝ) / 9) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 72) (by norm_num : (0 : ℝ) < 1 / 72)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48]

theorem int_2 : (∫ u in Ioc (((2 : ℝ) / 9) : ℝ) ((1 : ℝ) / 3), hatK (1 / 72) 289 vCert u) = ((163012945 : ℝ) / 10368) := by
  have h := hatK_run_integral (1 / 72) (by norm_num) 289 vCert 16 8
  rw [show (((16 : ℕ) : ℝ)) * (1 / 72) = (((2 : ℝ) / 9) : ℝ) by norm_num,
    show (((16 + 8 : ℕ) : ℝ)) * (1 / 72) = ((1 : ℝ) / 3) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 72) (by norm_num : (0 : ℝ) < 1 / 72)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48]

theorem int_3 : (∫ u in Ioc (((1 : ℝ) / 3) : ℝ) ((2 : ℝ) / 3), hatK (1 / 72) 289 vCert u) = ((6205573981 : ℝ) / 10368) := by
  have h := hatK_run_integral (1 / 72) (by norm_num) 289 vCert 24 24
  rw [show (((24 : ℕ) : ℝ)) * (1 / 72) = (((1 : ℝ) / 3) : ℝ) by norm_num,
    show (((24 + 24 : ℕ) : ℝ)) * (1 / 72) = ((2 : ℝ) / 3) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 72) (by norm_num : (0 : ℝ) < 1 / 72)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48]

/-- `hatGain(1/3) ≤ −1/100`. -/
theorem gain_bound : hatGain (1 / 3) lamC sigC (1 / 72) (2 / 9) (1 / 3) 289 vCert ≤ -(1 / 100) := by
  unfold hatGain
  have e2 : (2 : ℝ) * (1 / 3) / 2 = 1 / 3 := by norm_num
  have e1 : (2 : ℝ) * (1 / 3) = 2 / 3 := by norm_num
  have e3 : (2 / 9 : ℝ) / 2 = 1 / 9 := by norm_num
  have e4 : (1 / 3 : ℝ) / 2 = 1 / 6 := by norm_num
  rw [e2, e1, e3, e4, int_1, int_2, int_3]
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  obtain ⟨yl, -⟩ := exp_neg_enc ((2 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨y2, -⟩ := exp_neg_enc ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨y1, -⟩ := exp_neg_enc ((2 : ℝ) / 9) (by norm_num) (by norm_num)
  have cl := cT_lower ((2 : ℝ) / 3) _ 5 8 (by norm_num) yl (by norm_num) (by norm_num) (by norm_num)
  have c2 := cT_lower ((1 : ℝ) / 3) _ 2 5 (by norm_num) y2 (by norm_num) (by norm_num) (by norm_num)
  have c1 := cT_lower ((2 : ℝ) / 9) _ 1 3 (by norm_num) y1 (by norm_num) (by norm_num) (by norm_num)
  have s1 := sinh_lower ((1 : ℝ) / 9) (by norm_num) (by norm_num)
  have s2 := sinh_lower ((1 : ℝ) / 6) (by norm_num) (by norm_num)
  have s3 := sinh_lower ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  unfold lamC sigC
  norm_num at cl c2 c1 s1 s2 s3 ⊢
  linarith

theorem hat_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (1 / 3) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 100) * energy g.1 := by
  have hd := hat_diagonal g (1 / 3) a lamC sigC (1 / 72) (2 / 9) (1 / 3) 289 vCert
    (by norm_num) (by norm_num) (by linarith [log_two_lower]) (by norm_num) (by norm_num [sigC])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hm Q_all
  have hg := mul_le_mul_of_nonneg_right gain_bound (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`1/3` class.** -/
theorem universal_on_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (1 / 3) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := hat_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHatClass13V13

#print axioms AEGIS.RHHatClass13V13.Q_all
#print axioms AEGIS.RHHatClass13V13.gain_bound
#print axioms AEGIS.RHHatClass13V13.hat_coercive
#print axioms AEGIS.RHHatClass13V13.universal_on_class
