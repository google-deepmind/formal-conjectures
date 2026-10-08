import RHRatioWindowV13
import Mathlib.Tactic

/-!
AEGIS Ω — the ratio `33/16` lattice: eight prime-power-free windows, V13.

At packet log-half-width `1/256` (window radius `1/128`) the windows around
`(33/16)^k`, `k = 1, …, 8`, contain no prime power:

  k=1 [2.05, 2.08] ∅ · k=2 [4.22, 4.29] ∅ · k=3 [8.71, 8.84] ∅ · k=4 {18}
  k=5 [37.0, 37.6] ∅ · k=6 {77} · k=7 {158,159,160} · k=8 {325,…,330}

Every listed integer has `Λ = 0`, checked by kernel `decide`.  Hence on this
lattice the first eight gap cross terms carry no prime contribution at all.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHRatio33Over16V13
open AEGIS.RHRatioWindowV13

/-- The lattice ratio. -/
def q : ℝ := 33 / 16

theorem q_pos : 0 < q := by unfold q; norm_num
theorem log_two_le_log_q : Real.log 2 ≤ Real.log q := by
  apply Real.log_le_log (by norm_num) (by unfold q; norm_num)

theorem exp_one_div_128_le : Real.exp (1 / 128 : ℝ) ≤ 128 / 127 := by
  have := Real.exp_bound_div_one_sub_of_interval (x := (1 / 128 : ℝ)) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

theorem exp_neg_one_div_128_ge : (127 / 128 : ℝ) ≤ Real.exp (-(1 / 128 : ℝ)) := by
  linarith [Real.add_one_le_exp (-(1 / 128 : ℝ))]

/-- The window inequality pins `m` between rational multiples of `q^k`. -/
theorem window_bounds (k : ℕ) (m : ℕ) (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - k * Real.log q| ≤ 2 * (1 / 256)) :
    q ^ k * (127 / 128) ≤ (m : ℝ) ∧ (m : ℝ) ≤ q ^ k * (128 / 127) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hqk : (0 : ℝ) < q ^ k := pow_pos q_pos k
  have hlogq : Real.log (q ^ k) = k * Real.log q := by rw [Real.log_pow]
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  constructor
  · have := Real.exp_le_exp.mpr (show Real.log (q ^ k) - 1 / 128 ≤ Real.log (m : ℝ) by
      rw [hlogq]; linarith)
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hqk, Real.exp_log hmpos] at this
    calc q ^ k * (127 / 128) ≤ q ^ k * Real.exp (-(1 / 128 : ℝ)) :=
          mul_le_mul_of_nonneg_left exp_neg_one_div_128_ge hqk.le
      _ ≤ m := this
  · have := Real.exp_le_exp.mpr (show Real.log (m : ℝ) ≤ Real.log (q ^ k) + 1 / 128 by
      rw [hlogq]; linarith)
    rw [Real.exp_add, Real.exp_log hqk, Real.exp_log hmpos] at this
    calc (m : ℝ) ≤ q ^ k * Real.exp (1 / 128 : ℝ) := this
      _ ≤ q ^ k * (128 / 127) := mul_le_mul_of_nonneg_left exp_one_div_128_le hqk.le

/-- Integer enclosure of the window: `L ≤ m ≤ U` from the rational bounds. -/
theorem window_nat_bounds (k L U : ℕ) (hL : (L : ℝ) - 1 < q ^ k * (127 / 128))
    (hU : q ^ k * (128 / 127) < (U : ℝ) + 1) (m : ℕ) (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - k * Real.log q| ≤ 2 * (1 / 256)) :
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

/-- Windows `k = 1, 2, 3, 5` contain no integer at all. -/
theorem window_k1 : PrimePowerFreeWindow (1 * Real.log q) (1 / 256) := by
  intro m hm hw
  have := window_nat_bounds 1 3 2 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by simpa using hw)
  omega
theorem window_k2 : PrimePowerFreeWindow (2 * Real.log q) (1 / 256) := by
  intro m hm hw
  have := window_nat_bounds 2 5 4 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  omega
theorem window_k3 : PrimePowerFreeWindow (3 * Real.log q) (1 / 256) := by
  intro m hm hw
  have := window_nat_bounds 3 9 8 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  omega
theorem window_k5 : PrimePowerFreeWindow (5 * Real.log q) (1 / 256) := by
  intro m hm hw
  have := window_nat_bounds 5 38 37 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  omega

/-- Windows `k = 4, 6, 7, 8`: every integer inside has `Λ = 0`. -/
theorem window_k4 : PrimePowerFreeWindow (4 * Real.log q) (1 / 256) := by
  intro m hm hw
  have h := window_nat_bounds 4 18 18 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  have : m = 18 := by omega
  subst this
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  decide +kernel
theorem window_k6 : PrimePowerFreeWindow (6 * Real.log q) (1 / 256) := by
  intro m hm hw
  have h := window_nat_bounds 6 77 77 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  have : m = 77 := by omega
  subst this
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  decide +kernel
theorem window_k7 : PrimePowerFreeWindow (7 * Real.log q) (1 / 256) := by
  intro m hm hw
  have h := window_nat_bounds 7 158 160 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  obtain ⟨h1, h2⟩ := h
  interval_cases m <;> decide +kernel
theorem window_k8 : PrimePowerFreeWindow (8 * Real.log q) (1 / 256) := by
  intro m hm hw
  have h := window_nat_bounds 8 325 330 (by unfold q; norm_num) (by unfold q; norm_num) m hm
    (by exact_mod_cast hw)
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  obtain ⟨h1, h2⟩ := h
  interval_cases m <;> decide +kernel

/-- All eight gaps at once. -/
theorem window_all (k : ℕ) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    PrimePowerFreeWindow (k * Real.log q) (1 / 256) := by
  interval_cases k
  · exact_mod_cast window_k1
  · exact_mod_cast window_k2
  · exact_mod_cast window_k3
  · exact_mod_cast window_k4
  · exact_mod_cast window_k5
  · exact_mod_cast window_k6
  · exact_mod_cast window_k7
  · exact_mod_cast window_k8

end AEGIS.RHRatio33Over16V13

#print axioms AEGIS.RHRatio33Over16V13.window_all
