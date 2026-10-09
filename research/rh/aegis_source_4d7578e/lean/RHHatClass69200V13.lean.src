import RHHatCellsWideV13

/-!
AEGIS Ω — Weil positivity on the half-width-69/200 class via a positive-definite kernel, V13.

Certificate for `RHHatBudgetV13.hat_diagonal`: `h = 23/2800`, `n = 505` integer weights `vCert` (a
minimum-phase spectral factor, scaled by `10³`, of an LP-optimal positive-definite sequence;
`ρ_k` are checked by kernel evaluation of integer sums), `σ = 10⁻⁶`,
`λ = 4113/2000`, cap boundaries `t₁ = 23/100`, `t₂ = 69/200`.  The kernel condition holds on
`(0, 69/100]` by `Q_of_checksW` (336 sub-cells), the kernel integrals are exact trapezoid sums of
the autocorrelation values `ρ_k`, and `hatGain(69/200) ≤ −1/200`.
Every moment-zero packet of log-half-width `≤ 69/200` (support `≤ 69/100`) has `Re RHS ≤ −E/200`
and a nonnegative canonical zero quadratic.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatClass69200V13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13
open AEGIS.RHHatCellsV13
open AEGIS.RHHatCellsWideV13

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The integer weights, as a list. -/
def wL : List ℤ :=
  [73533, -31150, -6685, -7993, -5988, -4834, -1220, -11945, 310, 3477, -3530, -450,
   -4634, -2029, -939, -2168, 3698, -2113, -2033, -2792, 7246, -987, -2815, 7509,
   -7887, 5673, 3990, -3571, 4417, -3833, 2448, 3357, 2776, -3752, -2355, 6107,
   3257, -4446, 441, 1555, 254, 2301, -834, -3735, 6776, -3203, -1869, 3380,
   -475, -1562, 1479, -2941, 3572, -913, -2948, 2335, -1232, 116, 720, -1875,
   -227, 237, -407, -332, -1031, -18, -741, -2221, 1471, 140, -1936, 2414,
   -4493, 1345, 2182, -371, 679, -3349, -934, 656, -2912, -2730, -147, -1948,
   -10201, -94222, 65672, 26305, 18230, 14019, 7702, 4867, 6285, 747, -5251, 2395,
   -2364, 3766, 316, -2779, -803, -5228, -2918, 3037, -3879, -6642, -1702, 598,
   -8234, 5434, -5767, -3598, 1328, -2978, 2218, -2584, -2359, -198, 691, 3595,
   -6903, 2907, -101, 1147, 133, 756, -2598, 4460, -251, -1650, 2049, 2737,
   -3190, 4864, -1615, -1004, 4360, 223, -999, 2088, -2056, 4849, -2204, 2642,
   -2152, 1283, 3186, -1885, 1842, 596, -3299, 5045, 1684, -2241, -4426, 5838,
   -4849, 7248, -5578, -469, -734, 132, 2068, 5754, -4804, 3297, 1265, 321,
   3694, 16419, 66130, -79405, -44194, -19892, -10167, -3243, 3601, 12006, -3017, 11676,
   2688, 9413, -2283, 8687, 3011, 7143, -307, 9822, -827, 6546, -1526, 3825,
   3380, -850, 4490, -2395, -4927, 6439, -1802, 711, -3995, -1603, -3228, 9581,
   -8771, -1955, -4126, 7156, -3934, -4526, -2042, 6116, -10294, 5543, -5203, 4011,
   -4861, -421, -6631, 11896, -3628, -7081, -3160, 7950, 2047, -5257, -4010, 5781,
   -5793, 9596, -3372, -8863, 10355, -5776, 4081, 4334, -8910, 1846, 2792, 8368,
   -7792, 1786, 38, 1909, 1166, 1279, 2272, -3116, -10483, 12557, -1429, -493,
   -2513, -3296, -11734, -26651, 66650, 42430, 13751, -9403, -7449, -17872, -25948, 6932,
   -16822, -6031, -11009, 4724, -17221, 5261, -7731, 8777, -9317, -5210, 3827, 8803,
   -3347, -4536, 10677, -13377, 13659, 14676, -17988, 5659, 417, 9138, 5337, 378,
   -17347, 13623, 13898, -7206, -7627, 4774, 6659, 1462, -11872, 17409, -11072, 3599,
   -4412, 4545, 4705, 962, -20116, 11130, 9190, -755, -12936, -5381, 14827, -806,
   -9775, 8913, -15398, 5866, 13520, -19231, 10662, -10152, 1349, 6457, -1775, -4929,
   -6777, 7390, 3531, -10726, 9522, -6952, 1164, -5236, 9370, 8747, -16261, -503,
   4853, 3243, 2061, 1261, 6191, -40464, -24560, -4824, 26982, 14734, 18847, 24754,
   -12449, 13509, 2798, 3712, -7768, 16370, -15083, 2466, -11681, 3068, 12124, -17821,
   -8425, 4136, 2205, -11432, 16476, -19964, -14097, 24151, -4863, -4736, -6255, -6283,
   7572, 14457, -12307, -17420, 18101, 2924, -3373, -4094, -902, 14459, -20672, 14388,
   2784, -3284, -160, -7235, 7149, 18045, -17133, -6398, 5823, 11341, 3939, -17805,
   4791, 9446, -9077, 13530, -5574, -15545, 22692, -13654, 11882, -8184, 487, -3224,
   7390, 1746, -5642, -5425, 13858, -17509, 13895, -6609, 6353, -14886, 40, 12498,
   -9, -7227, -106, -293, 3485, -3194, 17231, 6373, -38, -23844, -9046, -7067,
   -11107, 12020, -4697, 1783, 2854, 4809, -7271, 13432, 99, 6155, 793, -12236,
   17596, 2163, -5106, 478, 4194, -11347, 15055, 4827, -17372, 2546, 4900, 730,
   3950, -8805, -6082, 6473, 10407, -14830, 1061, 1234, 986, 598, -8475, 13655,
   -11077, -3369, 7425, -2830, 5126, -7365, -7619, 12791, 1244, -4015, -6081, -449,
   11470, -4631, -4459, 5366, -6772, 3318, 10386, -14706, 8820, -6151, 6705, -3037,
   4819, -6781, 2174, 2546, 2578, -7483, 12161, -12345, 8749, -5596, 10680, -5467,
   -4599]

/-- The weights as a real sequence. -/
def vCert (i : ℕ) : ℝ := ((wL.getD i 0 : ℤ) : ℝ)

/-- `ρ_k` of the real weights is the cast of an integer sum. -/
theorem rhoZ (k : ℕ) : rhoK 505 vCert k =
    ((∑ j ∈ Finset.range 505, if j + k < 505 then wL.getD (j + k) 0 * wL.getD j 0 else 0 : ℤ) : ℝ) := by
  unfold rhoK vCert; push_cast; rfl

/-- The autocorrelation values `ρ_0 … ρ_84`. -/
def rv : ℕ → ℝ
  | 0 => 73766953866
  | 1 => -10179115689
  | 2 => -5873721711
  | 3 => -4019879690
  | 4 => -2999302485
  | 5 => -2355597287
  | 6 => -1913778034
  | 7 => -1591740781
  | 8 => -1347042885
  | 9 => -1154590233
  | 10 => -999196782
  | 11 => -871491493
  | 12 => -764433582
  | 13 => -673088449
  | 14 => -595013244
  | 15 => -526911475
  | 16 => -466886559
  | 17 => -414219669
  | 18 => -366704136
  | 19 => -324712002
  | 20 => -286416635
  | 21 => -251537732
  | 22 => -220050270
  | 23 => -191413031
  | 24 => -164718485
  | 25 => -140308632
  | 26 => -117640930
  | 27 => -96943170
  | 28 => -76925777
  | 29 => -59004651
  | 30 => -41845143
  | 31 => -25908650
  | 32 => -11000168
  | 33 => 3342739
  | 34 => 16508680
  | 35 => 29253022
  | 36 => 41196736
  | 37 => 52459196
  | 38 => 63388466
  | 39 => 73696127
  | 40 => 83464385
  | 41 => 92726223
  | 42 => 101736059
  | 43 => 110511666
  | 44 => 118709148
  | 45 => 126474031
  | 46 => 133869605
  | 47 => 141241046
  | 48 => 148360017
  | 49 => 155099671
  | 50 => 161311768
  | 51 => 167779760
  | 52 => 173656239
  | 53 => 179752559
  | 54 => 185306996
  | 55 => 190662374
  | 56 => 196145576
  | 57 => 201119439
  | 58 => 206574958
  | 59 => 211221935
  | 60 => 215999703
  | 61 => 220613290
  | 62 => 225305569
  | 63 => 229552522
  | 64 => 233726688
  | 65 => 238152846
  | 66 => 242348937
  | 67 => 246118879
  | 68 => 250258929
  | 69 => 253886033
  | 70 => 257739114
  | 71 => 261383348
  | 72 => 264836553
  | 73 => 268516969
  | 74 => 272050250
  | 75 => 275217527
  | 76 => 278757510
  | 77 => 281991474
  | 78 => 285050216
  | 79 => 288348747
  | 80 => 291445441
  | 81 => 294598997
  | 82 => 297638945
  | 83 => 300808885
  | 84 => 303576824
  | _ => 0

/-- `λ`. -/
def lamC : ℝ := ((4113 : ℝ) / 2000)

/-- `σ = 10⁻⁶`. -/
def sigC : ℝ := 1 / 1000000

set_option maxRecDepth 100000 in
theorem rho_0 : rhoK 505 vCert 0 = 73766953866 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 0 < 505 then wL.getD (j + 0) 0 * wL.getD j 0 else 0 : ℤ) = 73766953866)

set_option maxRecDepth 100000 in
theorem rho_1 : rhoK 505 vCert 1 = -10179115689 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 1 < 505 then wL.getD (j + 1) 0 * wL.getD j 0 else 0 : ℤ) = -10179115689)

set_option maxRecDepth 100000 in
theorem rho_2 : rhoK 505 vCert 2 = -5873721711 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 2 < 505 then wL.getD (j + 2) 0 * wL.getD j 0 else 0 : ℤ) = -5873721711)

set_option maxRecDepth 100000 in
theorem rho_3 : rhoK 505 vCert 3 = -4019879690 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 3 < 505 then wL.getD (j + 3) 0 * wL.getD j 0 else 0 : ℤ) = -4019879690)

set_option maxRecDepth 100000 in
theorem rho_4 : rhoK 505 vCert 4 = -2999302485 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 4 < 505 then wL.getD (j + 4) 0 * wL.getD j 0 else 0 : ℤ) = -2999302485)

set_option maxRecDepth 100000 in
theorem rho_5 : rhoK 505 vCert 5 = -2355597287 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 5 < 505 then wL.getD (j + 5) 0 * wL.getD j 0 else 0 : ℤ) = -2355597287)

set_option maxRecDepth 100000 in
theorem rho_6 : rhoK 505 vCert 6 = -1913778034 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 6 < 505 then wL.getD (j + 6) 0 * wL.getD j 0 else 0 : ℤ) = -1913778034)

set_option maxRecDepth 100000 in
theorem rho_7 : rhoK 505 vCert 7 = -1591740781 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 7 < 505 then wL.getD (j + 7) 0 * wL.getD j 0 else 0 : ℤ) = -1591740781)

set_option maxRecDepth 100000 in
theorem rho_8 : rhoK 505 vCert 8 = -1347042885 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 8 < 505 then wL.getD (j + 8) 0 * wL.getD j 0 else 0 : ℤ) = -1347042885)

set_option maxRecDepth 100000 in
theorem rho_9 : rhoK 505 vCert 9 = -1154590233 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 9 < 505 then wL.getD (j + 9) 0 * wL.getD j 0 else 0 : ℤ) = -1154590233)

set_option maxRecDepth 100000 in
theorem rho_10 : rhoK 505 vCert 10 = -999196782 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 10 < 505 then wL.getD (j + 10) 0 * wL.getD j 0 else 0 : ℤ) = -999196782)

set_option maxRecDepth 100000 in
theorem rho_11 : rhoK 505 vCert 11 = -871491493 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 11 < 505 then wL.getD (j + 11) 0 * wL.getD j 0 else 0 : ℤ) = -871491493)

set_option maxRecDepth 100000 in
theorem rho_12 : rhoK 505 vCert 12 = -764433582 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 12 < 505 then wL.getD (j + 12) 0 * wL.getD j 0 else 0 : ℤ) = -764433582)

set_option maxRecDepth 100000 in
theorem rho_13 : rhoK 505 vCert 13 = -673088449 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 13 < 505 then wL.getD (j + 13) 0 * wL.getD j 0 else 0 : ℤ) = -673088449)

set_option maxRecDepth 100000 in
theorem rho_14 : rhoK 505 vCert 14 = -595013244 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 14 < 505 then wL.getD (j + 14) 0 * wL.getD j 0 else 0 : ℤ) = -595013244)

set_option maxRecDepth 100000 in
theorem rho_15 : rhoK 505 vCert 15 = -526911475 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 15 < 505 then wL.getD (j + 15) 0 * wL.getD j 0 else 0 : ℤ) = -526911475)

set_option maxRecDepth 100000 in
theorem rho_16 : rhoK 505 vCert 16 = -466886559 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 16 < 505 then wL.getD (j + 16) 0 * wL.getD j 0 else 0 : ℤ) = -466886559)

set_option maxRecDepth 100000 in
theorem rho_17 : rhoK 505 vCert 17 = -414219669 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 17 < 505 then wL.getD (j + 17) 0 * wL.getD j 0 else 0 : ℤ) = -414219669)

set_option maxRecDepth 100000 in
theorem rho_18 : rhoK 505 vCert 18 = -366704136 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 18 < 505 then wL.getD (j + 18) 0 * wL.getD j 0 else 0 : ℤ) = -366704136)

set_option maxRecDepth 100000 in
theorem rho_19 : rhoK 505 vCert 19 = -324712002 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 19 < 505 then wL.getD (j + 19) 0 * wL.getD j 0 else 0 : ℤ) = -324712002)

set_option maxRecDepth 100000 in
theorem rho_20 : rhoK 505 vCert 20 = -286416635 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 20 < 505 then wL.getD (j + 20) 0 * wL.getD j 0 else 0 : ℤ) = -286416635)

set_option maxRecDepth 100000 in
theorem rho_21 : rhoK 505 vCert 21 = -251537732 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 21 < 505 then wL.getD (j + 21) 0 * wL.getD j 0 else 0 : ℤ) = -251537732)

set_option maxRecDepth 100000 in
theorem rho_22 : rhoK 505 vCert 22 = -220050270 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 22 < 505 then wL.getD (j + 22) 0 * wL.getD j 0 else 0 : ℤ) = -220050270)

set_option maxRecDepth 100000 in
theorem rho_23 : rhoK 505 vCert 23 = -191413031 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 23 < 505 then wL.getD (j + 23) 0 * wL.getD j 0 else 0 : ℤ) = -191413031)

set_option maxRecDepth 100000 in
theorem rho_24 : rhoK 505 vCert 24 = -164718485 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 24 < 505 then wL.getD (j + 24) 0 * wL.getD j 0 else 0 : ℤ) = -164718485)

set_option maxRecDepth 100000 in
theorem rho_25 : rhoK 505 vCert 25 = -140308632 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 25 < 505 then wL.getD (j + 25) 0 * wL.getD j 0 else 0 : ℤ) = -140308632)

set_option maxRecDepth 100000 in
theorem rho_26 : rhoK 505 vCert 26 = -117640930 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 26 < 505 then wL.getD (j + 26) 0 * wL.getD j 0 else 0 : ℤ) = -117640930)

set_option maxRecDepth 100000 in
theorem rho_27 : rhoK 505 vCert 27 = -96943170 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 27 < 505 then wL.getD (j + 27) 0 * wL.getD j 0 else 0 : ℤ) = -96943170)

set_option maxRecDepth 100000 in
theorem rho_28 : rhoK 505 vCert 28 = -76925777 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 28 < 505 then wL.getD (j + 28) 0 * wL.getD j 0 else 0 : ℤ) = -76925777)

set_option maxRecDepth 100000 in
theorem rho_29 : rhoK 505 vCert 29 = -59004651 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 29 < 505 then wL.getD (j + 29) 0 * wL.getD j 0 else 0 : ℤ) = -59004651)

set_option maxRecDepth 100000 in
theorem rho_30 : rhoK 505 vCert 30 = -41845143 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 30 < 505 then wL.getD (j + 30) 0 * wL.getD j 0 else 0 : ℤ) = -41845143)

set_option maxRecDepth 100000 in
theorem rho_31 : rhoK 505 vCert 31 = -25908650 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 31 < 505 then wL.getD (j + 31) 0 * wL.getD j 0 else 0 : ℤ) = -25908650)

set_option maxRecDepth 100000 in
theorem rho_32 : rhoK 505 vCert 32 = -11000168 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 32 < 505 then wL.getD (j + 32) 0 * wL.getD j 0 else 0 : ℤ) = -11000168)

set_option maxRecDepth 100000 in
theorem rho_33 : rhoK 505 vCert 33 = 3342739 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 33 < 505 then wL.getD (j + 33) 0 * wL.getD j 0 else 0 : ℤ) = 3342739)

set_option maxRecDepth 100000 in
theorem rho_34 : rhoK 505 vCert 34 = 16508680 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 34 < 505 then wL.getD (j + 34) 0 * wL.getD j 0 else 0 : ℤ) = 16508680)

set_option maxRecDepth 100000 in
theorem rho_35 : rhoK 505 vCert 35 = 29253022 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 35 < 505 then wL.getD (j + 35) 0 * wL.getD j 0 else 0 : ℤ) = 29253022)

set_option maxRecDepth 100000 in
theorem rho_36 : rhoK 505 vCert 36 = 41196736 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 36 < 505 then wL.getD (j + 36) 0 * wL.getD j 0 else 0 : ℤ) = 41196736)

set_option maxRecDepth 100000 in
theorem rho_37 : rhoK 505 vCert 37 = 52459196 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 37 < 505 then wL.getD (j + 37) 0 * wL.getD j 0 else 0 : ℤ) = 52459196)

set_option maxRecDepth 100000 in
theorem rho_38 : rhoK 505 vCert 38 = 63388466 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 38 < 505 then wL.getD (j + 38) 0 * wL.getD j 0 else 0 : ℤ) = 63388466)

set_option maxRecDepth 100000 in
theorem rho_39 : rhoK 505 vCert 39 = 73696127 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 39 < 505 then wL.getD (j + 39) 0 * wL.getD j 0 else 0 : ℤ) = 73696127)

set_option maxRecDepth 100000 in
theorem rho_40 : rhoK 505 vCert 40 = 83464385 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 40 < 505 then wL.getD (j + 40) 0 * wL.getD j 0 else 0 : ℤ) = 83464385)

set_option maxRecDepth 100000 in
theorem rho_41 : rhoK 505 vCert 41 = 92726223 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 41 < 505 then wL.getD (j + 41) 0 * wL.getD j 0 else 0 : ℤ) = 92726223)

set_option maxRecDepth 100000 in
theorem rho_42 : rhoK 505 vCert 42 = 101736059 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 42 < 505 then wL.getD (j + 42) 0 * wL.getD j 0 else 0 : ℤ) = 101736059)

set_option maxRecDepth 100000 in
theorem rho_43 : rhoK 505 vCert 43 = 110511666 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 43 < 505 then wL.getD (j + 43) 0 * wL.getD j 0 else 0 : ℤ) = 110511666)

set_option maxRecDepth 100000 in
theorem rho_44 : rhoK 505 vCert 44 = 118709148 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 44 < 505 then wL.getD (j + 44) 0 * wL.getD j 0 else 0 : ℤ) = 118709148)

set_option maxRecDepth 100000 in
theorem rho_45 : rhoK 505 vCert 45 = 126474031 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 45 < 505 then wL.getD (j + 45) 0 * wL.getD j 0 else 0 : ℤ) = 126474031)

set_option maxRecDepth 100000 in
theorem rho_46 : rhoK 505 vCert 46 = 133869605 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 46 < 505 then wL.getD (j + 46) 0 * wL.getD j 0 else 0 : ℤ) = 133869605)

set_option maxRecDepth 100000 in
theorem rho_47 : rhoK 505 vCert 47 = 141241046 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 47 < 505 then wL.getD (j + 47) 0 * wL.getD j 0 else 0 : ℤ) = 141241046)

set_option maxRecDepth 100000 in
theorem rho_48 : rhoK 505 vCert 48 = 148360017 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 48 < 505 then wL.getD (j + 48) 0 * wL.getD j 0 else 0 : ℤ) = 148360017)

set_option maxRecDepth 100000 in
theorem rho_49 : rhoK 505 vCert 49 = 155099671 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 49 < 505 then wL.getD (j + 49) 0 * wL.getD j 0 else 0 : ℤ) = 155099671)

set_option maxRecDepth 100000 in
theorem rho_50 : rhoK 505 vCert 50 = 161311768 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 50 < 505 then wL.getD (j + 50) 0 * wL.getD j 0 else 0 : ℤ) = 161311768)

set_option maxRecDepth 100000 in
theorem rho_51 : rhoK 505 vCert 51 = 167779760 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 51 < 505 then wL.getD (j + 51) 0 * wL.getD j 0 else 0 : ℤ) = 167779760)

set_option maxRecDepth 100000 in
theorem rho_52 : rhoK 505 vCert 52 = 173656239 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 52 < 505 then wL.getD (j + 52) 0 * wL.getD j 0 else 0 : ℤ) = 173656239)

set_option maxRecDepth 100000 in
theorem rho_53 : rhoK 505 vCert 53 = 179752559 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 53 < 505 then wL.getD (j + 53) 0 * wL.getD j 0 else 0 : ℤ) = 179752559)

set_option maxRecDepth 100000 in
theorem rho_54 : rhoK 505 vCert 54 = 185306996 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 54 < 505 then wL.getD (j + 54) 0 * wL.getD j 0 else 0 : ℤ) = 185306996)

set_option maxRecDepth 100000 in
theorem rho_55 : rhoK 505 vCert 55 = 190662374 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 55 < 505 then wL.getD (j + 55) 0 * wL.getD j 0 else 0 : ℤ) = 190662374)

set_option maxRecDepth 100000 in
theorem rho_56 : rhoK 505 vCert 56 = 196145576 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 56 < 505 then wL.getD (j + 56) 0 * wL.getD j 0 else 0 : ℤ) = 196145576)

set_option maxRecDepth 100000 in
theorem rho_57 : rhoK 505 vCert 57 = 201119439 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 57 < 505 then wL.getD (j + 57) 0 * wL.getD j 0 else 0 : ℤ) = 201119439)

set_option maxRecDepth 100000 in
theorem rho_58 : rhoK 505 vCert 58 = 206574958 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 58 < 505 then wL.getD (j + 58) 0 * wL.getD j 0 else 0 : ℤ) = 206574958)

set_option maxRecDepth 100000 in
theorem rho_59 : rhoK 505 vCert 59 = 211221935 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 59 < 505 then wL.getD (j + 59) 0 * wL.getD j 0 else 0 : ℤ) = 211221935)

set_option maxRecDepth 100000 in
theorem rho_60 : rhoK 505 vCert 60 = 215999703 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 60 < 505 then wL.getD (j + 60) 0 * wL.getD j 0 else 0 : ℤ) = 215999703)

set_option maxRecDepth 100000 in
theorem rho_61 : rhoK 505 vCert 61 = 220613290 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 61 < 505 then wL.getD (j + 61) 0 * wL.getD j 0 else 0 : ℤ) = 220613290)

set_option maxRecDepth 100000 in
theorem rho_62 : rhoK 505 vCert 62 = 225305569 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 62 < 505 then wL.getD (j + 62) 0 * wL.getD j 0 else 0 : ℤ) = 225305569)

set_option maxRecDepth 100000 in
theorem rho_63 : rhoK 505 vCert 63 = 229552522 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 63 < 505 then wL.getD (j + 63) 0 * wL.getD j 0 else 0 : ℤ) = 229552522)

set_option maxRecDepth 100000 in
theorem rho_64 : rhoK 505 vCert 64 = 233726688 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 64 < 505 then wL.getD (j + 64) 0 * wL.getD j 0 else 0 : ℤ) = 233726688)

set_option maxRecDepth 100000 in
theorem rho_65 : rhoK 505 vCert 65 = 238152846 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 65 < 505 then wL.getD (j + 65) 0 * wL.getD j 0 else 0 : ℤ) = 238152846)

set_option maxRecDepth 100000 in
theorem rho_66 : rhoK 505 vCert 66 = 242348937 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 66 < 505 then wL.getD (j + 66) 0 * wL.getD j 0 else 0 : ℤ) = 242348937)

set_option maxRecDepth 100000 in
theorem rho_67 : rhoK 505 vCert 67 = 246118879 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 67 < 505 then wL.getD (j + 67) 0 * wL.getD j 0 else 0 : ℤ) = 246118879)

set_option maxRecDepth 100000 in
theorem rho_68 : rhoK 505 vCert 68 = 250258929 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 68 < 505 then wL.getD (j + 68) 0 * wL.getD j 0 else 0 : ℤ) = 250258929)

set_option maxRecDepth 100000 in
theorem rho_69 : rhoK 505 vCert 69 = 253886033 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 69 < 505 then wL.getD (j + 69) 0 * wL.getD j 0 else 0 : ℤ) = 253886033)

set_option maxRecDepth 100000 in
theorem rho_70 : rhoK 505 vCert 70 = 257739114 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 70 < 505 then wL.getD (j + 70) 0 * wL.getD j 0 else 0 : ℤ) = 257739114)

set_option maxRecDepth 100000 in
theorem rho_71 : rhoK 505 vCert 71 = 261383348 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 71 < 505 then wL.getD (j + 71) 0 * wL.getD j 0 else 0 : ℤ) = 261383348)

set_option maxRecDepth 100000 in
theorem rho_72 : rhoK 505 vCert 72 = 264836553 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 72 < 505 then wL.getD (j + 72) 0 * wL.getD j 0 else 0 : ℤ) = 264836553)

set_option maxRecDepth 100000 in
theorem rho_73 : rhoK 505 vCert 73 = 268516969 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 73 < 505 then wL.getD (j + 73) 0 * wL.getD j 0 else 0 : ℤ) = 268516969)

set_option maxRecDepth 100000 in
theorem rho_74 : rhoK 505 vCert 74 = 272050250 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 74 < 505 then wL.getD (j + 74) 0 * wL.getD j 0 else 0 : ℤ) = 272050250)

set_option maxRecDepth 100000 in
theorem rho_75 : rhoK 505 vCert 75 = 275217527 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 75 < 505 then wL.getD (j + 75) 0 * wL.getD j 0 else 0 : ℤ) = 275217527)

set_option maxRecDepth 100000 in
theorem rho_76 : rhoK 505 vCert 76 = 278757510 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 76 < 505 then wL.getD (j + 76) 0 * wL.getD j 0 else 0 : ℤ) = 278757510)

set_option maxRecDepth 100000 in
theorem rho_77 : rhoK 505 vCert 77 = 281991474 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 77 < 505 then wL.getD (j + 77) 0 * wL.getD j 0 else 0 : ℤ) = 281991474)

set_option maxRecDepth 100000 in
theorem rho_78 : rhoK 505 vCert 78 = 285050216 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 78 < 505 then wL.getD (j + 78) 0 * wL.getD j 0 else 0 : ℤ) = 285050216)

set_option maxRecDepth 100000 in
theorem rho_79 : rhoK 505 vCert 79 = 288348747 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 79 < 505 then wL.getD (j + 79) 0 * wL.getD j 0 else 0 : ℤ) = 288348747)

set_option maxRecDepth 100000 in
theorem rho_80 : rhoK 505 vCert 80 = 291445441 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 80 < 505 then wL.getD (j + 80) 0 * wL.getD j 0 else 0 : ℤ) = 291445441)

set_option maxRecDepth 100000 in
theorem rho_81 : rhoK 505 vCert 81 = 294598997 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 81 < 505 then wL.getD (j + 81) 0 * wL.getD j 0 else 0 : ℤ) = 294598997)

set_option maxRecDepth 100000 in
theorem rho_82 : rhoK 505 vCert 82 = 297638945 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 82 < 505 then wL.getD (j + 82) 0 * wL.getD j 0 else 0 : ℤ) = 297638945)

set_option maxRecDepth 100000 in
theorem rho_83 : rhoK 505 vCert 83 = 300808885 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 83 < 505 then wL.getD (j + 83) 0 * wL.getD j 0 else 0 : ℤ) = 300808885)

set_option maxRecDepth 100000 in
theorem rho_84 : rhoK 505 vCert 84 = 303576824 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 505,
    if j + 84 < 505 then wL.getD (j + 84) 0 * wL.getD j 0 else 0 : ℤ) = 303576824)

set_option maxHeartbeats 4000000 in
theorem nodeV (k : ℕ) (hk : k ≤ 84) : hatK (23 / 2800) 505 vCert ((k : ℝ) * (23 / 2800)) = (23 / 2800) * rv k := by
  rw [hatK_node _ (by norm_num)]
  interval_cases k <;> norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rho_73, rho_74, rho_75, rho_76, rho_77, rho_78, rho_79, rho_80, rho_81, rho_82, rho_83, rho_84, rv]

set_option maxHeartbeats 20000000 in
theorem checks_0 : ∀ m : ℕ, m < 48 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_1 : ∀ m : ℕ, 48 ≤ m → m < 96 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_2 : ∀ m : ℕ, 96 ≤ m → m < 144 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_3 : ∀ m : ℕ, 144 ≤ m → m < 192 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_4 : ∀ m : ℕ, 192 ≤ m → m < 240 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_5 : ∀ m : ℕ, 240 ≤ m → m < 288 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_6 : ∀ m : ℕ, 288 ≤ m → m < 336 → 0 ≤ checkFW lamC sigC ((23 / 2800) * rv (m / 4))
    ((23 / 2800) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (23 / 2800)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

theorem Q_all : ∀ u ∈ Ioc (0 : ℝ) (2 * (69 / 200)), 0 ≤ kernelQ lamC sigC (23 / 2800) 505 vCert u := by
  have e : (2 : ℝ) * (69 / 200) = ((84 : ℕ) : ℝ) * (23 / 2800) := by norm_num
  rw [e]
  apply Q_of_checksW lamC sigC (23 / 2800) 505 vCert 84 4 rv (by norm_num) (by norm_num [sigC])
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
  by_cases h3 : m < 192
  · exact checks_3 m (by omega) h3
  push Not at h3
  by_cases h4 : m < 240
  · exact checks_4 m (by omega) h4
  push Not at h4
  by_cases h5 : m < 288
  · exact checks_5 m (by omega) h5
  push Not at h5
  exact checks_6 m (by omega) (by omega)

theorem int_1 : (∫ u in Ioc (0 : ℝ) ((23 : ℝ) / 100), hatK (23 / 2800) 505 vCert u) = ((-2181004606037 : ℝ) / 15680000) := by
  have h := hatK_run_integral (23 / 2800) (by norm_num) 505 vCert 0 28
  rw [show (((0 : ℕ) : ℝ)) * (23 / 2800) = (0 : ℝ) by norm_num,
    show (((0 + 28 : ℕ) : ℝ)) * (23 / 2800) = ((23 : ℝ) / 100) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (23 / 2800) (by norm_num : (0 : ℝ) < 23 / 2800)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rho_73, rho_74, rho_75, rho_76, rho_77, rho_78, rho_79, rho_80, rho_81, rho_82, rho_83, rho_84]

theorem int_2 : (∫ u in Ioc (((23 : ℝ) / 100) : ℝ) ((69 : ℝ) / 200), hatK (23 / 2800) 505 vCert u) = ((174930832487 : ℝ) / 7840000) := by
  have h := hatK_run_integral (23 / 2800) (by norm_num) 505 vCert 28 14
  rw [show (((28 : ℕ) : ℝ)) * (23 / 2800) = (((23 : ℝ) / 100) : ℝ) by norm_num,
    show (((28 + 14 : ℕ) : ℝ)) * (23 / 2800) = ((69 : ℝ) / 200) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (23 / 2800) (by norm_num : (0 : ℝ) < 23 / 2800)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rho_73, rho_74, rho_75, rho_76, rho_77, rho_78, rho_79, rho_80, rho_81, rho_82, rho_83, rho_84]

theorem int_3 : (∫ u in Ioc (((69 : ℝ) / 200) : ℝ) ((69 : ℝ) / 100), hatK (23 / 2800) 505 vCert u) = ((9823319036387 : ℝ) / 15680000) := by
  have h := hatK_run_integral (23 / 2800) (by norm_num) 505 vCert 42 42
  rw [show (((42 : ℕ) : ℝ)) * (23 / 2800) = (((69 : ℝ) / 200) : ℝ) by norm_num,
    show (((42 + 42 : ℕ) : ℝ)) * (23 / 2800) = ((69 : ℝ) / 100) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (23 / 2800) (by norm_num : (0 : ℝ) < 23 / 2800)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rho_73, rho_74, rho_75, rho_76, rho_77, rho_78, rho_79, rho_80, rho_81, rho_82, rho_83, rho_84]

/-- `hatGain(69/200) ≤ −1/200`. -/
theorem gain_bound : hatGain (69 / 200) lamC sigC (23 / 2800) (23 / 100) (69 / 200) 505 vCert ≤ -(1 / 200) := by
  unfold hatGain
  have e2 : (2 : ℝ) * (69 / 200) / 2 = 69 / 200 := by norm_num
  have e1 : (2 : ℝ) * (69 / 200) = 69 / 100 := by norm_num
  have e3 : (23 / 100 : ℝ) / 2 = 23 / 200 := by norm_num
  have e4 : (69 / 200 : ℝ) / 2 = 69 / 400 := by norm_num
  rw [e2, e1, e3, e4, int_1, int_2, int_3]
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  obtain ⟨yl, -⟩ := exp_neg_enc ((69 : ℝ) / 100) (by norm_num) (by norm_num)
  obtain ⟨y2, -⟩ := exp_neg_enc ((69 : ℝ) / 200) (by norm_num) (by norm_num)
  obtain ⟨y1, -⟩ := exp_neg_enc ((23 : ℝ) / 100) (by norm_num) (by norm_num)
  have cl := cT_lower ((69 : ℝ) / 100) _ 12 19 (by norm_num) yl (by norm_num) (by norm_num) (by norm_num)
  have c2 := cT_lower ((69 : ℝ) / 200) _ 11 28 (by norm_num) y2 (by norm_num) (by norm_num) (by norm_num)
  have c1 := cT_lower ((23 : ℝ) / 100) _ 8 25 (by norm_num) y1 (by norm_num) (by norm_num) (by norm_num)
  have s1 := sinh_lower ((23 : ℝ) / 200) (by norm_num) (by norm_num)
  have s2 := sinh_lower ((69 : ℝ) / 400) (by norm_num) (by norm_num)
  have s3 := sinh_lower ((69 : ℝ) / 200) (by norm_num) (by norm_num)
  unfold lamC sigC
  norm_num at cl c2 c1 s1 s2 s3 ⊢
  linarith

theorem hat_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (69 / 200) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 200) * energy g.1 := by
  have hd := hat_diagonal g (69 / 200) a lamC sigC (23 / 2800) (23 / 100) (69 / 200) 505 vCert
    (by norm_num) (by norm_num) (by have h2 := Real.log_two_gt_d9; norm_num at h2 ⊢; linarith) (by norm_num) (by norm_num [sigC])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hm Q_all
  have hg := mul_le_mul_of_nonneg_right gain_bound (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`69/200` class.** -/
theorem universal_on_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (69 / 200) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := hat_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHatClass69200V13

#print axioms AEGIS.RHHatClass69200V13.Q_all
#print axioms AEGIS.RHHatClass69200V13.gain_bound
#print axioms AEGIS.RHHatClass69200V13.hat_coercive
#print axioms AEGIS.RHHatClass69200V13.universal_on_class
