import RHHatCellsWideV13
import RHHatCoxBudgetV13

/-!
AEGIS Ω — Weil positivity on the half-width-693/2000 class via a positive-definite kernel, V13.

Certificate for `RHHatCoxBudgetV13.hatcox_diagonal` (Coxeter caps `1, 93/100, 91/100, 87/100, 81/100, 71/100, 1/2` ≥ `cos(π/(N+1))`): `h = 77/8000`, `n = 433` integer weights `vCert` (a
minimum-phase spectral factor, scaled by `10³`, of an LP-optimal positive-definite sequence;
`ρ_k` are checked by kernel evaluation of integer sums), `σ = 10⁻⁶`,
`λ = 10227/5000`, cap boundaries `s₇…s₂ = 847/8000, 231/2000, 231/1600, 693/4000, 231/1000, 693/2000`.  The kernel condition holds on
`(0, 693/1000]` by `Q_of_checksW` (288 sub-cells), the kernel integrals are exact trapezoid sums of
the autocorrelation values `ρ_k`, and `hatCoxGain(693/2000) ≤ −1/200`.
Every moment-zero packet of log-half-width `≤ 693/2000` (support `≤ 693/1000`) has `Re RHS ≤ −E/200`
and a nonnegative canonical zero quadratic.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatCoxClass693V13
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
open AEGIS.RHHatCoxBudgetV13

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The integer weights, as a list. -/
def wL : List ℤ :=
  [63113, -23903, -8244, -2974, -6490, -3160, -8905, 1257, 618, -7153, -1401, 6007,
   -5360, -4961, 2808, -2120, -913, 1231, 850, -3722, 4100, 213, 906, -1002,
   1323, 3353, -902, 786, -577, 3154, 1406, -2814, 1992, 2108, 647, -1626,
   889, 1014, 1592, -2399, 836, 3263, -3762, 1997, 215, -525, -387, 1905,
   -1861, -714, 2761, -3383, 905, -334, -1057, 576, -1161, -908, 1155, -401,
   -3169, 2107, 737, -270, -1746, 209, -2827, 627, -323, -4563, -611, -610,
   -9489, -79209, 55196, 21462, 16093, 11195, 4126, 7593, 1403, -2165, 4879, -2670,
   -4293, 2476, 2524, -4149, -1120, -962, -4508, -481, -665, -4866, -1353, -1011,
   -3167, 550, -3178, -1647, 266, 1067, -3593, -317, 3101, -3417, 1293, -1147,
   1264, 1130, -1961, 2296, -119, -657, 449, 3965, -3097, 374, 4129, -1185,
   -634, 2036, 822, 1096, 87, 1247, -377, 3401, -1559, -679, 3660, -1836,
   -527, 4206, -2743, -2010, 2405, 1812, -512, 930, 2898, -943, 2490, -270,
   3695, 12389, 58527, -74120, -29469, -23612, -5528, 5066, 4883, -3598, 8199, 5689,
   6517, 1785, 5397, 1437, 3134, 6131, 2706, 1561, 1836, 4320, 765, 1763,
   -3833, 8433, -2995, -4625, 5826, -4201, 2316, -3344, -2789, 3135, 200, -6536,
   -103, 4371, -5344, -497, -3165, 3261, -68, -5673, -403, 3138, -2123, -2828,
   1925, -4559, 5813, -2651, -5603, 4880, -1137, 2643, -7616, 5981, 1409, -3363,
   989, 3001, -3907, 2166, 6663, -7058, -1520, 5989, 703, -8771, 5196, 3004,
   917, -8892, -5154, -28253, 70725, 23250, 15544, -8705, -19533, -16123, 4307, -14053,
   -10951, -6934, 2628, -10268, -401, 2777, -9939, 1834, 4792, -2596, -2214, 2794,
   -89, 11649, -13616, 3711, 13947, -8022, 5126, -8294, 15371, 1029, -10622, 3446,
   10700, 157, -13736, 12611, 267, -22, -3779, 177, 6531, -4040, -545, 1782,
   -3302, 1310, 8347, -16660, 7349, 5401, -6026, -2127, -2236, 9126, -9335, 875,
   -903, 1983, -4270, 3843, -1561, -11488, 15383, -1172, -11734, 3547, 10012, -7344,
   -6020, 1578, 10627, -2856, 9801, -50122, -7059, -566, 18160, 23449, 15122, -5132,
   11016, 5319, 4662, -9721, 10283, -5568, -8184, 10767, -9044, -5360, 352, -275,
   -1599, -1309, -15243, 17160, -1834, -17912, 9111, -1607, 10814, -21290, 4760, 12401,
   -3716, -11813, 2929, 17117, -17049, 3907, 2404, 1222, 971, -3388, 4200, -2035,
   485, 6848, -5324, -7691, 19887, -11208, -1506, 2846, 3803, 423, -6423, 6527,
   -3008, 5077, -5027, 2457, -3100, 1114, 11424, -20246, 4971, 11052, -8863, -3224,
   4618, 4239, -3416, -5167, 2981, -2250, 23316, -4346, -5006, -13203, -12343, -4828,
   4976, -2687, 1425, -2164, 11118, -7969, 8381, 4885, -6984, 8383, 225, 2074,
   -945, -1109, 1080, 9852, -12928, -728, 12983, -7696, -813, -6518, 13734, -5769,
   -7324, 2227, 7431, -4343, -9440, 11723, -4739, -2148, 1760, -1584, 846, -1375,
   1934, -1171, -4196, 4913, 3158, -10912, 8136, -1043, -81, -1391, -450, 3288,
   -2120, 2320, -4152, 4339, -378, 1133, -548, -6183, 14253, -5860, -4944, 7470,
   -5632]

/-- The weights as a real sequence. -/
def vCert (i : ℕ) : ℝ := ((wL.getD i 0 : ℤ) : ℝ)

/-- `ρ_k` of the real weights is the cast of an integer sum. -/
theorem rhoZ (k : ℕ) : rhoK 433 vCert k =
    ((∑ j ∈ Finset.range 433, if j + k < 433 then wL.getD (j + k) 0 * wL.getD j 0 else 0 : ℤ) : ℝ) := by
  unfold rhoK vCert; push_cast; rfl

/-- The autocorrelation values `ρ_0 … ρ_72`. -/
def rv : ℕ → ℝ
  | 0 => 50640914215
  | 1 => -7362370301
  | 2 => -4226196469
  | 3 => -2876088434
  | 4 => -2132666487
  | 5 => -1663913091
  | 6 => -1342151655
  | 7 => -1107454681
  | 8 => -929039687
  | 9 => -788903381
  | 10 => -675664068
  | 11 => -582503080
  | 12 => -504530448
  | 13 => -438048464
  | 14 => -380994323
  | 15 => -331190457
  | 16 => -287652423
  | 17 => -249064732
  | 18 => -214452895
  | 19 => -183642189
  | 20 => -155808395
  | 21 => -130297661
  | 22 => -107143958
  | 23 => -85982045
  | 24 => -66750505
  | 25 => -49130783
  | 26 => -32383644
  | 27 => -16923560
  | 28 => -2373806
  | 29 => 10735115
  | 30 => 23441139
  | 31 => 35330817
  | 32 => 46490699
  | 33 => 56792456
  | 34 => 66712221
  | 35 => 76115901
  | 36 => 84726045
  | 37 => 93569840
  | 38 => 101322537
  | 39 => 109044600
  | 40 => 116407285
  | 41 => 123228478
  | 42 => 130004970
  | 43 => 136583445
  | 44 => 142767008
  | 45 => 148501258
  | 46 => 154397125
  | 47 => 159878268
  | 48 => 165150983
  | 49 => 170069189
  | 50 => 174841723
  | 51 => 179742499
  | 52 => 184569074
  | 53 => 189231722
  | 54 => 193500240
  | 55 => 197682168
  | 56 => 201979912
  | 57 => 205915341
  | 58 => 209719236
  | 59 => 213593404
  | 60 => 217343768
  | 61 => 221027840
  | 62 => 224469494
  | 63 => 228027046
  | 64 => 231468090
  | 65 => 234718320
  | 66 => 238007330
  | 67 => 241365521
  | 68 => 244422838
  | 69 => 247443455
  | 70 => 250451638
  | 71 => 253410809
  | 72 => 256579655
  | _ => 0

/-- `λ`. -/
def lamC : ℝ := ((10227 : ℝ) / 5000)

/-- `σ = 10⁻⁶`. -/
def sigC : ℝ := 1 / 1000000

set_option maxRecDepth 100000 in
theorem rho_0 : rhoK 433 vCert 0 = 50640914215 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 0 < 433 then wL.getD (j + 0) 0 * wL.getD j 0 else 0 : ℤ) = 50640914215)

set_option maxRecDepth 100000 in
theorem rho_1 : rhoK 433 vCert 1 = -7362370301 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 1 < 433 then wL.getD (j + 1) 0 * wL.getD j 0 else 0 : ℤ) = -7362370301)

set_option maxRecDepth 100000 in
theorem rho_2 : rhoK 433 vCert 2 = -4226196469 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 2 < 433 then wL.getD (j + 2) 0 * wL.getD j 0 else 0 : ℤ) = -4226196469)

set_option maxRecDepth 100000 in
theorem rho_3 : rhoK 433 vCert 3 = -2876088434 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 3 < 433 then wL.getD (j + 3) 0 * wL.getD j 0 else 0 : ℤ) = -2876088434)

set_option maxRecDepth 100000 in
theorem rho_4 : rhoK 433 vCert 4 = -2132666487 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 4 < 433 then wL.getD (j + 4) 0 * wL.getD j 0 else 0 : ℤ) = -2132666487)

set_option maxRecDepth 100000 in
theorem rho_5 : rhoK 433 vCert 5 = -1663913091 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 5 < 433 then wL.getD (j + 5) 0 * wL.getD j 0 else 0 : ℤ) = -1663913091)

set_option maxRecDepth 100000 in
theorem rho_6 : rhoK 433 vCert 6 = -1342151655 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 6 < 433 then wL.getD (j + 6) 0 * wL.getD j 0 else 0 : ℤ) = -1342151655)

set_option maxRecDepth 100000 in
theorem rho_7 : rhoK 433 vCert 7 = -1107454681 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 7 < 433 then wL.getD (j + 7) 0 * wL.getD j 0 else 0 : ℤ) = -1107454681)

set_option maxRecDepth 100000 in
theorem rho_8 : rhoK 433 vCert 8 = -929039687 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 8 < 433 then wL.getD (j + 8) 0 * wL.getD j 0 else 0 : ℤ) = -929039687)

set_option maxRecDepth 100000 in
theorem rho_9 : rhoK 433 vCert 9 = -788903381 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 9 < 433 then wL.getD (j + 9) 0 * wL.getD j 0 else 0 : ℤ) = -788903381)

set_option maxRecDepth 100000 in
theorem rho_10 : rhoK 433 vCert 10 = -675664068 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 10 < 433 then wL.getD (j + 10) 0 * wL.getD j 0 else 0 : ℤ) = -675664068)

set_option maxRecDepth 100000 in
theorem rho_11 : rhoK 433 vCert 11 = -582503080 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 11 < 433 then wL.getD (j + 11) 0 * wL.getD j 0 else 0 : ℤ) = -582503080)

set_option maxRecDepth 100000 in
theorem rho_12 : rhoK 433 vCert 12 = -504530448 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 12 < 433 then wL.getD (j + 12) 0 * wL.getD j 0 else 0 : ℤ) = -504530448)

set_option maxRecDepth 100000 in
theorem rho_13 : rhoK 433 vCert 13 = -438048464 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 13 < 433 then wL.getD (j + 13) 0 * wL.getD j 0 else 0 : ℤ) = -438048464)

set_option maxRecDepth 100000 in
theorem rho_14 : rhoK 433 vCert 14 = -380994323 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 14 < 433 then wL.getD (j + 14) 0 * wL.getD j 0 else 0 : ℤ) = -380994323)

set_option maxRecDepth 100000 in
theorem rho_15 : rhoK 433 vCert 15 = -331190457 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 15 < 433 then wL.getD (j + 15) 0 * wL.getD j 0 else 0 : ℤ) = -331190457)

set_option maxRecDepth 100000 in
theorem rho_16 : rhoK 433 vCert 16 = -287652423 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 16 < 433 then wL.getD (j + 16) 0 * wL.getD j 0 else 0 : ℤ) = -287652423)

set_option maxRecDepth 100000 in
theorem rho_17 : rhoK 433 vCert 17 = -249064732 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 17 < 433 then wL.getD (j + 17) 0 * wL.getD j 0 else 0 : ℤ) = -249064732)

set_option maxRecDepth 100000 in
theorem rho_18 : rhoK 433 vCert 18 = -214452895 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 18 < 433 then wL.getD (j + 18) 0 * wL.getD j 0 else 0 : ℤ) = -214452895)

set_option maxRecDepth 100000 in
theorem rho_19 : rhoK 433 vCert 19 = -183642189 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 19 < 433 then wL.getD (j + 19) 0 * wL.getD j 0 else 0 : ℤ) = -183642189)

set_option maxRecDepth 100000 in
theorem rho_20 : rhoK 433 vCert 20 = -155808395 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 20 < 433 then wL.getD (j + 20) 0 * wL.getD j 0 else 0 : ℤ) = -155808395)

set_option maxRecDepth 100000 in
theorem rho_21 : rhoK 433 vCert 21 = -130297661 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 21 < 433 then wL.getD (j + 21) 0 * wL.getD j 0 else 0 : ℤ) = -130297661)

set_option maxRecDepth 100000 in
theorem rho_22 : rhoK 433 vCert 22 = -107143958 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 22 < 433 then wL.getD (j + 22) 0 * wL.getD j 0 else 0 : ℤ) = -107143958)

set_option maxRecDepth 100000 in
theorem rho_23 : rhoK 433 vCert 23 = -85982045 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 23 < 433 then wL.getD (j + 23) 0 * wL.getD j 0 else 0 : ℤ) = -85982045)

set_option maxRecDepth 100000 in
theorem rho_24 : rhoK 433 vCert 24 = -66750505 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 24 < 433 then wL.getD (j + 24) 0 * wL.getD j 0 else 0 : ℤ) = -66750505)

set_option maxRecDepth 100000 in
theorem rho_25 : rhoK 433 vCert 25 = -49130783 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 25 < 433 then wL.getD (j + 25) 0 * wL.getD j 0 else 0 : ℤ) = -49130783)

set_option maxRecDepth 100000 in
theorem rho_26 : rhoK 433 vCert 26 = -32383644 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 26 < 433 then wL.getD (j + 26) 0 * wL.getD j 0 else 0 : ℤ) = -32383644)

set_option maxRecDepth 100000 in
theorem rho_27 : rhoK 433 vCert 27 = -16923560 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 27 < 433 then wL.getD (j + 27) 0 * wL.getD j 0 else 0 : ℤ) = -16923560)

set_option maxRecDepth 100000 in
theorem rho_28 : rhoK 433 vCert 28 = -2373806 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 28 < 433 then wL.getD (j + 28) 0 * wL.getD j 0 else 0 : ℤ) = -2373806)

set_option maxRecDepth 100000 in
theorem rho_29 : rhoK 433 vCert 29 = 10735115 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 29 < 433 then wL.getD (j + 29) 0 * wL.getD j 0 else 0 : ℤ) = 10735115)

set_option maxRecDepth 100000 in
theorem rho_30 : rhoK 433 vCert 30 = 23441139 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 30 < 433 then wL.getD (j + 30) 0 * wL.getD j 0 else 0 : ℤ) = 23441139)

set_option maxRecDepth 100000 in
theorem rho_31 : rhoK 433 vCert 31 = 35330817 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 31 < 433 then wL.getD (j + 31) 0 * wL.getD j 0 else 0 : ℤ) = 35330817)

set_option maxRecDepth 100000 in
theorem rho_32 : rhoK 433 vCert 32 = 46490699 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 32 < 433 then wL.getD (j + 32) 0 * wL.getD j 0 else 0 : ℤ) = 46490699)

set_option maxRecDepth 100000 in
theorem rho_33 : rhoK 433 vCert 33 = 56792456 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 33 < 433 then wL.getD (j + 33) 0 * wL.getD j 0 else 0 : ℤ) = 56792456)

set_option maxRecDepth 100000 in
theorem rho_34 : rhoK 433 vCert 34 = 66712221 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 34 < 433 then wL.getD (j + 34) 0 * wL.getD j 0 else 0 : ℤ) = 66712221)

set_option maxRecDepth 100000 in
theorem rho_35 : rhoK 433 vCert 35 = 76115901 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 35 < 433 then wL.getD (j + 35) 0 * wL.getD j 0 else 0 : ℤ) = 76115901)

set_option maxRecDepth 100000 in
theorem rho_36 : rhoK 433 vCert 36 = 84726045 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 36 < 433 then wL.getD (j + 36) 0 * wL.getD j 0 else 0 : ℤ) = 84726045)

set_option maxRecDepth 100000 in
theorem rho_37 : rhoK 433 vCert 37 = 93569840 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 37 < 433 then wL.getD (j + 37) 0 * wL.getD j 0 else 0 : ℤ) = 93569840)

set_option maxRecDepth 100000 in
theorem rho_38 : rhoK 433 vCert 38 = 101322537 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 38 < 433 then wL.getD (j + 38) 0 * wL.getD j 0 else 0 : ℤ) = 101322537)

set_option maxRecDepth 100000 in
theorem rho_39 : rhoK 433 vCert 39 = 109044600 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 39 < 433 then wL.getD (j + 39) 0 * wL.getD j 0 else 0 : ℤ) = 109044600)

set_option maxRecDepth 100000 in
theorem rho_40 : rhoK 433 vCert 40 = 116407285 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 40 < 433 then wL.getD (j + 40) 0 * wL.getD j 0 else 0 : ℤ) = 116407285)

set_option maxRecDepth 100000 in
theorem rho_41 : rhoK 433 vCert 41 = 123228478 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 41 < 433 then wL.getD (j + 41) 0 * wL.getD j 0 else 0 : ℤ) = 123228478)

set_option maxRecDepth 100000 in
theorem rho_42 : rhoK 433 vCert 42 = 130004970 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 42 < 433 then wL.getD (j + 42) 0 * wL.getD j 0 else 0 : ℤ) = 130004970)

set_option maxRecDepth 100000 in
theorem rho_43 : rhoK 433 vCert 43 = 136583445 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 43 < 433 then wL.getD (j + 43) 0 * wL.getD j 0 else 0 : ℤ) = 136583445)

set_option maxRecDepth 100000 in
theorem rho_44 : rhoK 433 vCert 44 = 142767008 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 44 < 433 then wL.getD (j + 44) 0 * wL.getD j 0 else 0 : ℤ) = 142767008)

set_option maxRecDepth 100000 in
theorem rho_45 : rhoK 433 vCert 45 = 148501258 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 45 < 433 then wL.getD (j + 45) 0 * wL.getD j 0 else 0 : ℤ) = 148501258)

set_option maxRecDepth 100000 in
theorem rho_46 : rhoK 433 vCert 46 = 154397125 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 46 < 433 then wL.getD (j + 46) 0 * wL.getD j 0 else 0 : ℤ) = 154397125)

set_option maxRecDepth 100000 in
theorem rho_47 : rhoK 433 vCert 47 = 159878268 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 47 < 433 then wL.getD (j + 47) 0 * wL.getD j 0 else 0 : ℤ) = 159878268)

set_option maxRecDepth 100000 in
theorem rho_48 : rhoK 433 vCert 48 = 165150983 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 48 < 433 then wL.getD (j + 48) 0 * wL.getD j 0 else 0 : ℤ) = 165150983)

set_option maxRecDepth 100000 in
theorem rho_49 : rhoK 433 vCert 49 = 170069189 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 49 < 433 then wL.getD (j + 49) 0 * wL.getD j 0 else 0 : ℤ) = 170069189)

set_option maxRecDepth 100000 in
theorem rho_50 : rhoK 433 vCert 50 = 174841723 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 50 < 433 then wL.getD (j + 50) 0 * wL.getD j 0 else 0 : ℤ) = 174841723)

set_option maxRecDepth 100000 in
theorem rho_51 : rhoK 433 vCert 51 = 179742499 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 51 < 433 then wL.getD (j + 51) 0 * wL.getD j 0 else 0 : ℤ) = 179742499)

set_option maxRecDepth 100000 in
theorem rho_52 : rhoK 433 vCert 52 = 184569074 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 52 < 433 then wL.getD (j + 52) 0 * wL.getD j 0 else 0 : ℤ) = 184569074)

set_option maxRecDepth 100000 in
theorem rho_53 : rhoK 433 vCert 53 = 189231722 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 53 < 433 then wL.getD (j + 53) 0 * wL.getD j 0 else 0 : ℤ) = 189231722)

set_option maxRecDepth 100000 in
theorem rho_54 : rhoK 433 vCert 54 = 193500240 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 54 < 433 then wL.getD (j + 54) 0 * wL.getD j 0 else 0 : ℤ) = 193500240)

set_option maxRecDepth 100000 in
theorem rho_55 : rhoK 433 vCert 55 = 197682168 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 55 < 433 then wL.getD (j + 55) 0 * wL.getD j 0 else 0 : ℤ) = 197682168)

set_option maxRecDepth 100000 in
theorem rho_56 : rhoK 433 vCert 56 = 201979912 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 56 < 433 then wL.getD (j + 56) 0 * wL.getD j 0 else 0 : ℤ) = 201979912)

set_option maxRecDepth 100000 in
theorem rho_57 : rhoK 433 vCert 57 = 205915341 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 57 < 433 then wL.getD (j + 57) 0 * wL.getD j 0 else 0 : ℤ) = 205915341)

set_option maxRecDepth 100000 in
theorem rho_58 : rhoK 433 vCert 58 = 209719236 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 58 < 433 then wL.getD (j + 58) 0 * wL.getD j 0 else 0 : ℤ) = 209719236)

set_option maxRecDepth 100000 in
theorem rho_59 : rhoK 433 vCert 59 = 213593404 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 59 < 433 then wL.getD (j + 59) 0 * wL.getD j 0 else 0 : ℤ) = 213593404)

set_option maxRecDepth 100000 in
theorem rho_60 : rhoK 433 vCert 60 = 217343768 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 60 < 433 then wL.getD (j + 60) 0 * wL.getD j 0 else 0 : ℤ) = 217343768)

set_option maxRecDepth 100000 in
theorem rho_61 : rhoK 433 vCert 61 = 221027840 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 61 < 433 then wL.getD (j + 61) 0 * wL.getD j 0 else 0 : ℤ) = 221027840)

set_option maxRecDepth 100000 in
theorem rho_62 : rhoK 433 vCert 62 = 224469494 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 62 < 433 then wL.getD (j + 62) 0 * wL.getD j 0 else 0 : ℤ) = 224469494)

set_option maxRecDepth 100000 in
theorem rho_63 : rhoK 433 vCert 63 = 228027046 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 63 < 433 then wL.getD (j + 63) 0 * wL.getD j 0 else 0 : ℤ) = 228027046)

set_option maxRecDepth 100000 in
theorem rho_64 : rhoK 433 vCert 64 = 231468090 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 64 < 433 then wL.getD (j + 64) 0 * wL.getD j 0 else 0 : ℤ) = 231468090)

set_option maxRecDepth 100000 in
theorem rho_65 : rhoK 433 vCert 65 = 234718320 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 65 < 433 then wL.getD (j + 65) 0 * wL.getD j 0 else 0 : ℤ) = 234718320)

set_option maxRecDepth 100000 in
theorem rho_66 : rhoK 433 vCert 66 = 238007330 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 66 < 433 then wL.getD (j + 66) 0 * wL.getD j 0 else 0 : ℤ) = 238007330)

set_option maxRecDepth 100000 in
theorem rho_67 : rhoK 433 vCert 67 = 241365521 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 67 < 433 then wL.getD (j + 67) 0 * wL.getD j 0 else 0 : ℤ) = 241365521)

set_option maxRecDepth 100000 in
theorem rho_68 : rhoK 433 vCert 68 = 244422838 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 68 < 433 then wL.getD (j + 68) 0 * wL.getD j 0 else 0 : ℤ) = 244422838)

set_option maxRecDepth 100000 in
theorem rho_69 : rhoK 433 vCert 69 = 247443455 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 69 < 433 then wL.getD (j + 69) 0 * wL.getD j 0 else 0 : ℤ) = 247443455)

set_option maxRecDepth 100000 in
theorem rho_70 : rhoK 433 vCert 70 = 250451638 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 70 < 433 then wL.getD (j + 70) 0 * wL.getD j 0 else 0 : ℤ) = 250451638)

set_option maxRecDepth 100000 in
theorem rho_71 : rhoK 433 vCert 71 = 253410809 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 71 < 433 then wL.getD (j + 71) 0 * wL.getD j 0 else 0 : ℤ) = 253410809)

set_option maxRecDepth 100000 in
theorem rho_72 : rhoK 433 vCert 72 = 256579655 := by
  rw [rhoZ]
  exact_mod_cast (by decide +kernel : (∑ j ∈ Finset.range 433,
    if j + 72 < 433 then wL.getD (j + 72) 0 * wL.getD j 0 else 0 : ℤ) = 256579655)

set_option maxHeartbeats 4000000 in
theorem nodeV (k : ℕ) (hk : k ≤ 72) : hatK (77 / 8000) 433 vCert ((k : ℝ) * (77 / 8000)) = (77 / 8000) * rv k := by
  rw [hatK_node _ (by norm_num)]
  interval_cases k <;> norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rv]

set_option maxHeartbeats 20000000 in
theorem checks_0 : ∀ m : ℕ, m < 48 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_1 : ∀ m : ℕ, 48 ≤ m → m < 96 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_2 : ∀ m : ℕ, 96 ≤ m → m < 144 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_3 : ∀ m : ℕ, 144 ≤ m → m < 192 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_4 : ∀ m : ℕ, 192 ≤ m → m < 240 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_5 : ∀ m : ℕ, 240 ≤ m → m < 288 → 0 ≤ checkFW lamC sigC ((77 / 8000) * rv (m / 4))
    ((77 / 8000) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (77 / 8000)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkFW, expNegLo, rv, lamC, sigC, min_def]

theorem Q_all : ∀ u ∈ Ioc (0 : ℝ) (2 * (693 / 2000)), 0 ≤ kernelQ lamC sigC (77 / 8000) 433 vCert u := by
  have e : (2 : ℝ) * (693 / 2000) = ((72 : ℕ) : ℝ) * (77 / 8000) := by norm_num
  rw [e]
  apply Q_of_checksW lamC sigC (77 / 8000) 433 vCert 72 4 rv (by norm_num) (by norm_num [sigC])
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
  exact checks_5 m (by omega) (by omega)

theorem int_1 : (∫ u in Ioc (0 : ℝ) ((847 : ℝ) / 8000), hatK (77 / 8000) 433 vCert u) = ((22823772223483 : ℝ) / 128000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 0 11
  rw [show (((0 : ℕ) : ℝ)) * (77 / 8000) = (0 : ℝ) by norm_num,
    show (((0 + 11 : ℕ) : ℝ)) * (77 / 8000) = ((847 : ℝ) / 8000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_2 : (∫ u in Ioc (((847 : ℝ) / 8000) : ℝ) ((231 : ℝ) / 2000), hatK (77 / 8000) 433 vCert u) = ((-805627723439 : ℝ) / 16000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 11 1
  rw [show (((11 : ℕ) : ℝ)) * (77 / 8000) = (((847 : ℝ) / 8000) : ℝ) by norm_num,
    show (((11 + 1 : ℕ) : ℝ)) * (77 / 8000) = ((231 : ℝ) / 2000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_3 : (∫ u in Ioc (((231 : ℝ) / 2000) : ℝ) ((231 : ℝ) / 1600), hatK (77 / 8000) 433 vCert u) = ((-14667198613991 : ℝ) / 128000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 12 3
  rw [show (((12 : ℕ) : ℝ)) * (77 / 8000) = (((231 : ℝ) / 2000) : ℝ) by norm_num,
    show (((12 + 3 : ℕ) : ℝ)) * (77 / 8000) = ((231 : ℝ) / 1600) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_4 : (∫ u in Ioc (((231 : ℝ) / 1600) : ℝ) ((693 : ℝ) / 4000), hatK (77 / 8000) 433 vCert u) = ((-4799755728999 : ℝ) / 64000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 15 3
  rw [show (((15 : ℕ) : ℝ)) * (77 / 8000) = (((231 : ℝ) / 1600) : ℝ) by norm_num,
    show (((15 + 3 : ℕ) : ℝ)) * (77 / 8000) = ((693 : ℝ) / 4000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_5 : (∫ u in Ioc (((693 : ℝ) / 4000) : ℝ) ((231 : ℝ) / 1000), hatK (77 / 8000) 433 vCert u) = ((-1190952223923 : ℝ) / 16000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 18 6
  rw [show (((18 : ℕ) : ℝ)) * (77 / 8000) = (((693 : ℝ) / 4000) : ℝ) by norm_num,
    show (((18 + 6 : ℕ) : ℝ)) * (77 / 8000) = ((231 : ℝ) / 1000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_6 : (∫ u in Ioc (((231 : ℝ) / 1000) : ℝ) ((693 : ℝ) / 2000), hatK (77 / 8000) 433 vCert u) = ((53075062117 : ℝ) / 2560000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 24 12
  rw [show (((24 : ℕ) : ℝ)) * (77 / 8000) = (((231 : ℝ) / 1000) : ℝ) by norm_num,
    show (((24 + 12 : ℕ) : ℝ)) * (77 / 8000) = ((693 : ℝ) / 2000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

theorem int_7 : (∫ u in Ioc (((693 : ℝ) / 2000) : ℝ) ((693 : ℝ) / 1000), hatK (77 / 8000) 433 vCert u) = ((4968879457927 : ℝ) / 8000000) := by
  have h := hatK_run_integral (77 / 8000) (by norm_num) 433 vCert 36 36
  rw [show (((36 : ℕ) : ℝ)) * (77 / 8000) = (((693 : ℝ) / 2000) : ℝ) by norm_num,
    show (((36 + 36 : ℕ) : ℝ)) * (77 / 8000) = ((693 : ℝ) / 1000) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (77 / 8000) (by norm_num : (0 : ℝ) < 77 / 8000)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72]

/-- `hatCoxGain(693/2000) ≤ −1/200`. -/
theorem gain_bound : hatCoxGain (693 / 2000) lamC sigC (77 / 8000) (847 / 8000) (231 / 2000) (231 / 1600) (693 / 4000) (231 / 1000) (693 / 2000) 433 vCert ≤ -(1 / 200) := by
  unfold hatCoxGain firstGain regionGain
  have e1 : (2 : ℝ) * (693 / 2000) = 693 / 1000 := by norm_num
  have eh0 : (847 / 8000 : ℝ) / 2 = 847 / 16000 := by norm_num
  have eh1 : (231 / 2000 : ℝ) / 2 = 231 / 4000 := by norm_num
  have eh2 : (231 / 1600 : ℝ) / 2 = 231 / 3200 := by norm_num
  have eh3 : (693 / 4000 : ℝ) / 2 = 693 / 8000 := by norm_num
  have eh4 : (231 / 1000 : ℝ) / 2 = 231 / 2000 := by norm_num
  have eh5 : (693 / 2000 : ℝ) / 2 = 693 / 4000 := by norm_num
  have eh6 : (693 / 1000 : ℝ) / 2 = 693 / 2000 := by norm_num
  rw [e1, eh0, eh1, eh2, eh3, eh4, eh5, eh6, int_1, int_2, int_3, int_4, int_5, int_6, int_7]
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  obtain ⟨y0, -⟩ := exp_neg_enc ((847 : ℝ) / 8000) (by norm_num) (by norm_num)
  have c0 := cT_lower ((847 : ℝ) / 8000) _ 9 38 (by norm_num) y0 (by norm_num) (by norm_num) (by norm_num)
  have s0 := sinh_lower ((847 : ℝ) / 16000) (by norm_num) (by norm_num)
  obtain ⟨y1, -⟩ := exp_neg_enc ((231 : ℝ) / 2000) (by norm_num) (by norm_num)
  have c1 := cT_lower ((231 : ℝ) / 2000) _ 9 37 (by norm_num) y1 (by norm_num) (by norm_num) (by norm_num)
  have s1 := sinh_lower ((231 : ℝ) / 4000) (by norm_num) (by norm_num)
  obtain ⟨y2, -⟩ := exp_neg_enc ((231 : ℝ) / 1600) (by norm_num) (by norm_num)
  have c2 := cT_lower ((231 : ℝ) / 1600) _ 9 34 (by norm_num) y2 (by norm_num) (by norm_num) (by norm_num)
  have s2 := sinh_lower ((231 : ℝ) / 3200) (by norm_num) (by norm_num)
  obtain ⟨y3, -⟩ := exp_neg_enc ((693 : ℝ) / 4000) (by norm_num) (by norm_num)
  have c3 := cT_lower ((693 : ℝ) / 4000) _ 2 7 (by norm_num) y3 (by norm_num) (by norm_num) (by norm_num)
  have s3 := sinh_lower ((693 : ℝ) / 8000) (by norm_num) (by norm_num)
  obtain ⟨y4, -⟩ := exp_neg_enc ((231 : ℝ) / 1000) (by norm_num) (by norm_num)
  have c4 := cT_lower ((231 : ℝ) / 1000) _ 9 28 (by norm_num) y4 (by norm_num) (by norm_num) (by norm_num)
  have s4 := sinh_lower ((231 : ℝ) / 2000) (by norm_num) (by norm_num)
  obtain ⟨y5, -⟩ := exp_neg_enc ((693 : ℝ) / 2000) (by norm_num) (by norm_num)
  have c5 := cT_lower ((693 : ℝ) / 2000) _ 2 5 (by norm_num) y5 (by norm_num) (by norm_num) (by norm_num)
  have s5 := sinh_lower ((693 : ℝ) / 4000) (by norm_num) (by norm_num)
  obtain ⟨y6, -⟩ := exp_neg_enc ((693 : ℝ) / 1000) (by norm_num) (by norm_num)
  have c6 := cT_lower ((693 : ℝ) / 1000) _ 12 19 (by norm_num) y6 (by norm_num) (by norm_num) (by norm_num)
  have s6 := sinh_lower ((693 : ℝ) / 2000) (by norm_num) (by norm_num)
  unfold lamC sigC
  norm_num at c0 c1 c2 c3 c4 c5 c6 s0 s1 s2 s3 s4 s5 s6 ⊢
  linarith

theorem hat_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (693 / 2000) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 200) * energy g.1 := by
  have hd := hatcox_diagonal g (693 / 2000) a lamC sigC (77 / 8000) (847 / 8000) (231 / 2000) (231 / 1600) (693 / 4000) (231 / 1000) (693 / 2000) 433 vCert
    (by norm_num) (by norm_num) (by have h2 := Real.log_two_gt_d9; norm_num at h2 ⊢; linarith)
    (by norm_num) (by norm_num [sigC]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hm Q_all
  have hg := mul_le_mul_of_nonneg_right gain_bound (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`693/2000` class.** -/
theorem universal_on_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (693 / 2000) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := hat_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHatCoxClass693V13

#print axioms AEGIS.RHHatCoxClass693V13.Q_all
#print axioms AEGIS.RHHatCoxClass693V13.gain_bound
#print axioms AEGIS.RHHatCoxClass693V13.hat_coercive
#print axioms AEGIS.RHHatCoxClass693V13.universal_on_class
