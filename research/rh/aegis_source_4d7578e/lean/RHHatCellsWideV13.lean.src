import RHHatCellsV13

/-!
AEGIS Ω — widened sub-cell checks for hat-kernel certificates, V13.

`RHHatCellsV13.Q_of_checks` encloses `e^{−3b/2}` by a Taylor polynomial valid for `3b/2 ≤ 1`, so it
stops at `Nh ≤ 2/3`.  Here `e^{−3b/2} = (e^{−3b/4})²` is bounded below by the square of the
fourth-order enclosure at `3b/4`, valid for `b ≤ 4/3`.  `Q_of_checksW` is the same sweep with this
check `checkFW`, up to `Nh ≤ 4/3`; certificates can now reach the whole prime-free range `2r < log 2`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatCellsWideV13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13
open AEGIS.RHHatCellsV13

/-- The fourth-order lower enclosure of `e^{−x}`. -/
def expNegLo (x : ℝ) : ℝ := 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 100

theorem expNegLo_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ expNegLo x := by
  unfold expNegLo
  have h2 : 0 ≤ x ^ 2 := by positivity
  have h3 : x ^ 3 ≤ x ^ 2 := by nlinarith
  have h4 : 0 ≤ x ^ 4 := by positivity
  have h5 : x ^ 5 ≤ x ^ 2 := by nlinarith [pow_le_one₀ hx0 hx1 (n := 3)]
  nlinarith

theorem expNeg_sq_lower (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 4 / 3) :
    expNegLo (3 * b / 4) ^ 2 ≤ Real.exp (-(3 * b / 2)) := by
  obtain ⟨hlo, -⟩ := exp_neg_enc (3 * b / 4) (by linarith) (by linarith)
  have h0 := expNegLo_nonneg (3 * b / 4) (by linarith) (by linarith)
  have hsq : Real.exp (-(3 * b / 2)) = Real.exp (-(3 * b / 4)) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [hsq]
  unfold expNegLo at h0 ⊢
  exact pow_le_pow_left₀ h0 hlo 2

/-- The widened rational check for one sub-cell with right endpoint `b`. -/
def checkFW (lam σ A B θa θb b : ℝ) : ℝ :=
  2 / ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) -
      expNegLo (3 * b / 4) ^ 2) -
    lam * ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) +
      (1 - b / 2 + (b / 2) ^ 2 / 2 - (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100)) +
    σ * min (A + θa * (B - A)) (A + θb * (B - A))

/-- One widened sub-cell of the kernel check. -/
theorem cell_QW (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (θa θb A B b : ℝ) (hh : 0 < h)
    (hσ : 0 ≤ σ) (hl : 0 ≤ lam) (hA : hatK h n v ((k : ℝ) * h) = A)
    (hB : hatK h n v (((k + 1 : ℕ) : ℝ) * h) = B) (hθa : 0 ≤ θa) (hθab : θa ≤ θb)
    (hθb : θb ≤ 1) (hb : b = (k + θb) * h) (hb0 : 0 < b) (hb1 : b ≤ 4 / 3)
    (hcheck : 0 ≤ checkFW lam σ A B θa θb b)
    (u : ℝ) (hu1 : (k + θa) * h ≤ u) (hu2 : u ≤ b) (hu0 : 0 < u) :
    0 ≤ kernelQ lam σ h n v u := by
  unfold kernelQ
  unfold checkFW at hcheck
  obtain ⟨-, he⟩ := exp_pos_enc (b / 2) (by linarith) (by linarith)
  have hn3 := expNeg_sq_lower b hb0 hb1
  obtain ⟨-, hn1⟩ := exp_neg_enc (b / 2) (by linarith) (by linarith)
  have hmono := ehs_anti u b hu0 hu2
  have hd : 0 < Real.exp (b / 2) - Real.exp (-(3 * b / 2)) := by
    rw [sub_pos, Real.exp_lt_exp]; linarith
  have hfrac : 2 / ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 +
          (b / 2) ^ 5 / 100) - expNegLo (3 * b / 4) ^ 2) ≤
        2 / (Real.exp (b / 2) - Real.exp (-(3 * b / 2))) := by
    apply div_le_div_of_nonneg_left (by norm_num) hd
    linarith
  have hcosh : Real.cosh (u / 2) ≤ Real.cosh (b / 2) := by
    rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have hcb : 2 * Real.cosh (b / 2) ≤
      (1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) +
        (1 - b / 2 + (b / 2) ^ 2 / 2 - (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) := by
    rw [Real.cosh_eq]; linarith
  have hk : min (A + θa * (B - A)) (A + θb * (B - A)) ≤ hatK h n v u := by
    have hta := mul_nonneg hθa hh.le
    have htb := mul_le_mul_of_nonneg_right hθb hh.le
    rw [hb] at hu2
    have hkh1 : (k : ℝ) * h ≤ u := by linarith
    have hkh2 : u ≤ ((k : ℝ) + 1) * h := by linarith
    have haff := hatK_affine h hh n v k u hkh1 hkh2
    push_cast at hB
    rw [haff, hA, hB]
    set θ := (u - k * h) / h with hθ
    have hθ1 : θa ≤ θ := by rw [hθ, le_div_iff₀ hh]; linarith
    have hθ2 : θ ≤ θb := by rw [hθ, div_le_iff₀ hh]; linarith
    have e : ((k + 1) * h - u) / h * A + θ * B = A + θ * (B - A) := by
      rw [hθ]; field_simp; ring
    rw [e]
    rcases le_total A B with hAB | hAB
    · have hm1 := mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hAB)
      have hid : θ * (B - A) - θa * (B - A) = (θ - θa) * (B - A) := by ring
      have hle : A + θa * (B - A) ≤ A + θ * (B - A) := by linarith
      exact le_trans (min_le_left _ _) hle
    · have hm2 := mul_nonneg (sub_nonneg.2 hθ2) (sub_nonneg.2 hAB)
      have hid : θ * (B - A) - θb * (B - A) = (θb - θ) * (A - B) := by ring
      have hle : A + θb * (B - A) ≤ A + θ * (B - A) := by linarith
      exact le_trans (min_le_right _ _) hle
  have h1 := mul_le_mul_of_nonneg_left hk hσ
  have h2 := mul_le_mul_of_nonneg_left hcb hl
  have h3 := mul_le_mul_of_nonneg_left hcosh hl
  linarith

/-- **Widened sub-cell checks imply the kernel condition on `(0, Nh]`, `Nh ≤ 4/3`.** -/
theorem Q_of_checksW (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (N s : ℕ) (rv : ℕ → ℝ) (hh : 0 < h)
    (hσ : 0 ≤ σ) (hl : 0 ≤ lam) (hs : 0 < s) (hNh : (N : ℝ) * h ≤ 4 / 3)
    (hnode : ∀ k : ℕ, k ≤ N → hatK h n v ((k : ℝ) * h) = h * rv k)
    (hcheck : ∀ m : ℕ, m < N * s → 0 ≤ checkFW lam σ (h * rv (m / s)) (h * rv (m / s + 1))
      (((m % s : ℕ) : ℝ) / s) (((m % s + 1 : ℕ) : ℝ) / s) ((((m + 1 : ℕ) : ℝ) / s) * h)) :
    ∀ u ∈ Ioc (0 : ℝ) (N * h), 0 ≤ kernelQ lam σ h n v u := by
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  set c : ℝ := s / h with hc
  have hc0 : 0 < c := div_pos hsR hh
  have hcu : 0 < c * u := mul_pos hc0 hu0
  have hcuN : c * u ≤ (N * s : ℕ) := by
    push_cast
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hh]
    nlinarith
  have hpos : 0 < ⌈c * u⌉₊ := Nat.ceil_pos.mpr hcu
  have hle : ⌈c * u⌉₊ ≤ N * s := Nat.ceil_le.mpr hcuN
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈c * u⌉₊ = m + 1 := ⟨⌈c * u⌉₊ - 1, by omega⟩
  have hm1 : (m : ℝ) < c * u := by
    have h1 := Nat.ceil_lt_add_one hcu.le
    rw [hm] at h1; push_cast at h1; linarith
  have hm2 : c * u ≤ (m : ℝ) + 1 := by
    have h2 := Nat.le_ceil (c * u)
    rw [hm] at h2; push_cast at h2; linarith
  have hmN : m < N * s := by omega
  set k := m / s with hk
  set j := m % s with hj
  have hdm : s * k + j = m := Nat.div_add_mod m s
  have hjs : j < s := Nat.mod_lt m hs
  have hkN : k < N := by rw [hk]; exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hmN)
  have hdmR : (s : ℝ) * k + j = m := by exact_mod_cast hdm
  have hjsR : (j : ℝ) + 1 ≤ s := by exact_mod_cast hjs
  have hbeq : ((((m + 1 : ℕ) : ℝ) / s) * h) = (k + ((j + 1 : ℕ) : ℝ) / s) * h := by
    push_cast; rw [← hdmR]; field_simp; ring
  have hmh : (m : ℝ) * h < s * u := by
    have := mul_lt_mul_of_pos_right hm1 hh
    rw [hc, div_mul_eq_mul_div, mul_comm (s : ℝ) u] at this
    rw [mul_div_assoc] at this
    field_simp at this
    linarith
  have hmh2 : s * u ≤ ((m : ℝ) + 1) * h := by
    have := mul_le_mul_of_nonneg_right hm2 hh.le
    rw [hc] at this
    field_simp at this
    linarith
  apply cell_QW lam σ h n v k ((j : ℝ) / s) (((j + 1 : ℕ) : ℝ) / s) (h * rv k) (h * rv (k + 1))
    ((((m + 1 : ℕ) : ℝ) / s) * h) hh hσ hl (hnode k hkN.le) (hnode (k + 1) hkN)
    (by positivity)
    (by apply div_le_div_of_nonneg_right _ hsR.le; push_cast; linarith)
    (by rw [div_le_one hsR]; push_cast; linarith) hbeq
    (by positivity)
    (by
      have : (((m + 1 : ℕ) : ℝ) / s) ≤ N := by
        rw [div_le_iff₀ hsR]
        have : m + 1 ≤ N * s := hmN
        exact_mod_cast this
      nlinarith)
    (hcheck m hmN) u
    (by
      rw [show ((k : ℝ) + j / s) * h = (s * k + j) / s * h by field_simp, hdmR]
      rw [div_mul_eq_mul_div, div_le_iff₀ hsR]; linarith)
    (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsR]; push_cast; linarith)
    hu0

end AEGIS.RHHatCellsWideV13

#print axioms AEGIS.RHHatCellsWideV13.expNeg_sq_lower
#print axioms AEGIS.RHHatCellsWideV13.cell_QW
#print axioms AEGIS.RHHatCellsWideV13.Q_of_checksW
