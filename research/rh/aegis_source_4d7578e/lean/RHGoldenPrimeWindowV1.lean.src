import RHRatioWindowV13
import Mathlib.Tactic

/-!
AEGIS Ω — the golden lattice `q = φ² = (3 + √5)/2`: three prime-power-free windows, V1.

At packet log-half-width `1/128` (window radius `1/64`) the windows around
`q^k`, `k = 1, 2, 3`, contain no prime power:

  k=1 q  ≈ 2.618   [2.577, 2.660]  ∅
  k=2 q² ≈ 6.854   [6.747, 6.963]  ∅
  k=3 q³ ≈ 17.944  [17.664, 18.229] {18},  Λ(18) = 0

At half-width `1/64` (radius `1/32`) the `k = 2` window reaches `7.07 > 7` and
contains the prime `7`, so `1/128` is the widest dyadic half-width that works.
The `k = 3` window is checked by kernel `decide`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGoldenPrimeWindowV1
open AEGIS.RHRatioWindowV13

/-- The golden lattice ratio `φ² = (3 + √5)/2`. -/
def q : ℝ := (3 + Real.sqrt 5) / 2

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_lower : (2236 / 1000 : ℝ) < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt5_upper : Real.sqrt 5 < 2237 / 1000 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem q_sq : q ^ 2 = (7 + 3 * Real.sqrt 5) / 2 := by
  unfold q; nlinarith [sqrt5_sq]

theorem q_cube : q ^ 3 = 9 + 4 * Real.sqrt 5 := by
  unfold q; linear_combination (Real.sqrt 5 + 9) / 8 * sqrt5_sq

theorem q_pos : 0 < q := by unfold q; positivity

theorem log_two_le_log_q : Real.log 2 ≤ Real.log q := by
  apply Real.log_le_log (by norm_num)
  unfold q; linarith [sqrt5_lower]

theorem exp_one_div_64_le : Real.exp (1 / 64 : ℝ) ≤ 64 / 63 := by
  have := Real.exp_bound_div_one_sub_of_interval (x := (1 / 64 : ℝ)) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

theorem exp_neg_one_div_64_ge : (63 / 64 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) := by
  linarith [Real.add_one_le_exp (-(1 / 64 : ℝ))]

/-- The window inequality pins `m` between rational multiples of `q^k`. -/
theorem window_bounds (k : ℕ) (m : ℕ) (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - k * Real.log q| ≤ 2 * (1 / 128)) :
    q ^ k * (63 / 64) ≤ (m : ℝ) ∧ (m : ℝ) ≤ q ^ k * (64 / 63) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hqk : (0 : ℝ) < q ^ k := pow_pos q_pos k
  have hlogq : Real.log (q ^ k) = k * Real.log q := by rw [Real.log_pow]
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  constructor
  · have := Real.exp_le_exp.mpr (show Real.log (q ^ k) - 1 / 64 ≤ Real.log (m : ℝ) by
      rw [hlogq]; linarith)
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hqk, Real.exp_log hmpos] at this
    calc q ^ k * (63 / 64) ≤ q ^ k * Real.exp (-(1 / 64 : ℝ)) :=
          mul_le_mul_of_nonneg_left exp_neg_one_div_64_ge hqk.le
      _ ≤ m := this
  · have := Real.exp_le_exp.mpr (show Real.log (m : ℝ) ≤ Real.log (q ^ k) + 1 / 64 by
      rw [hlogq]; linarith)
    rw [Real.exp_add, Real.exp_log hqk, Real.exp_log hmpos] at this
    calc (m : ℝ) ≤ q ^ k * Real.exp (1 / 64 : ℝ) := this
      _ ≤ q ^ k * (64 / 63) := mul_le_mul_of_nonneg_left exp_one_div_64_le hqk.le

/-- Integer enclosure of the window: `L ≤ m ≤ U` from the rational bounds. -/
theorem window_nat_bounds (k L U : ℕ) (hL : (L : ℝ) - 1 < q ^ k * (63 / 64))
    (hU : q ^ k * (64 / 63) < (U : ℝ) + 1) (m : ℕ) (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - k * Real.log q| ≤ 2 * (1 / 128)) :
    L ≤ m ∧ m ≤ U := by
  obtain ⟨h1, h2⟩ := window_bounds k m hm hw
  have hl : (L : ℝ) - 1 < m := lt_of_lt_of_le hL h1
  have hu : (m : ℝ) < U + 1 := lt_of_le_of_lt h2 hU
  constructor
  · have : (L : ℝ) < m + 1 := by linarith
    have : L < m + 1 := by exact_mod_cast this
    omega
  · have : m < U + 1 := by exact_mod_cast hu
    omega

/-- `k = 1`: the window `[2.577, 2.660]` contains no integer. -/
theorem window_k1 : PrimePowerFreeWindow (1 * Real.log q) (1 / 128) := by
  intro m hm hw
  have := window_nat_bounds 1 3 2
    (by rw [pow_one]; unfold q; push_cast; linarith [sqrt5_lower])
    (by rw [pow_one]; unfold q; push_cast; linarith [sqrt5_upper]) m hm
    (by simpa using hw)
  omega

/-- `k = 2`: the window `[6.747, 6.963]` contains no integer (the prime `7` is outside). -/
theorem window_k2 : PrimePowerFreeWindow (2 * Real.log q) (1 / 128) := by
  intro m hm hw
  have := window_nat_bounds 2 7 6
    (by rw [q_sq]; push_cast; linarith [sqrt5_lower])
    (by rw [q_sq]; push_cast; linarith [sqrt5_upper]) m hm
    (by exact_mod_cast hw)
  omega

/-- `k = 3`: the only integer in `[17.664, 18.229]` is `18`, and `Λ(18) = 0`. -/
theorem window_k3 : PrimePowerFreeWindow (3 * Real.log q) (1 / 128) := by
  intro m hm hw
  have h := window_nat_bounds 3 18 18
    (by rw [q_cube]; push_cast; linarith [sqrt5_lower])
    (by rw [q_cube]; push_cast; linarith [sqrt5_upper]) m hm
    (by exact_mod_cast hw)
  have : m = 18 := by omega
  subst this
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  decide +kernel

/-- All three golden gaps at once. -/
theorem window_all (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    PrimePowerFreeWindow (k * Real.log q) (1 / 128) := by
  interval_cases k
  · exact_mod_cast window_k1
  · exact_mod_cast window_k2
  · exact_mod_cast window_k3

end AEGIS.RHGoldenPrimeWindowV1

#print axioms AEGIS.RHGoldenPrimeWindowV1.window_all
