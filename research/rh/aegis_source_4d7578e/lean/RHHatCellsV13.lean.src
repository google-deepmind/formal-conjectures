import RHHatBudgetV13

/-!
AEGIS Ω — sub-cell checks for positive-definite hat-kernel certificates, V13.

`Q_of_checks`: to prove `Q(u) = e^{u/2}/sinh u − 2λ cosh(u/2) + σ·hatK(u) ≥ 0` on `(0, Nh]` it
suffices to check, for each of the `N·s` sub-cells `[mh/s, (m+1)h/s]`, one rational inequality
`checkF ≥ 0` built from the kernel's node values, the monotonicity of `e^{u/2}/sinh u` and
`cosh(u/2)`, and fourth-order Taylor enclosures of `exp` at the right endpoint.  Also:
`cT_lower` (a `cothTail` lower bound from `log x ≥ 1 − 1/x`) and `sinh_lower`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatCellsV13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13

theorem ehs_eq (u : ℝ) (hu : 0 < u) :
    Real.exp (u / 2) / Real.sinh u = 2 / (Real.exp (u / 2) - Real.exp (-(3 * u / 2))) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hd : 0 < Real.exp (u / 2) - Real.exp (-(3 * u / 2)) := by
    rw [sub_pos, Real.exp_lt_exp]; linarith
  rw [div_eq_div_iff hs.ne' hd.ne', Real.sinh_eq]
  have e1 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (u / 2) * Real.exp (-(3 * u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [e1, e2]

theorem ehs_anti (u b : ℝ) (hu : 0 < u) (hub : u ≤ b) :
    2 / (Real.exp (b / 2) - Real.exp (-(3 * b / 2))) ≤ Real.exp (u / 2) / Real.sinh u := by
  rw [ehs_eq u hu]
  have hd : 0 < Real.exp (u / 2) - Real.exp (-(3 * u / 2)) := by
    rw [sub_pos, Real.exp_lt_exp]; linarith
  apply div_le_div_of_nonneg_left (by norm_num) hd
  have h1 : Real.exp (u / 2) ≤ Real.exp (b / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(3 * b / 2)) ≤ Real.exp (-(3 * u / 2)) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- One sub-cell of the kernel check. -/
theorem cell_Q (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (θa θb A B b : ℝ) (hh : 0 < h)
    (hσ : 0 ≤ σ) (hl : 0 ≤ lam) (hA : hatK h n v ((k : ℝ) * h) = A)
    (hB : hatK h n v (((k + 1 : ℕ) : ℝ) * h) = B) (hθa : 0 ≤ θa) (hθab : θa ≤ θb)
    (hθb : θb ≤ 1) (hb : b = (k + θb) * h) (hb0 : 0 < b) (hb1 : b ≤ 2 / 3)
    (hcheck : 0 ≤ 2 / ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 +
          (b / 2) ^ 5 / 100) -
        (1 - 3 * b / 2 + (3 * b / 2) ^ 2 / 2 - (3 * b / 2) ^ 3 / 6 + (3 * b / 2) ^ 4 / 24 -
          (3 * b / 2) ^ 5 / 100)) -
      lam * ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 +
          (b / 2) ^ 5 / 100) +
        (1 - b / 2 + (b / 2) ^ 2 / 2 - (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100)) +
      σ * min (A + θa * (B - A)) (A + θb * (B - A)))
    (u : ℝ) (hu1 : (k + θa) * h ≤ u) (hu2 : u ≤ b) (hu0 : 0 < u) :
    0 ≤ kernelQ lam σ h n v u := by
  unfold kernelQ
  obtain ⟨-, he⟩ := exp_pos_enc (b / 2) (by linarith) (by linarith)
  obtain ⟨hn3, -⟩ := exp_neg_enc (3 * b / 2) (by linarith) (by linarith)
  obtain ⟨-, hn1⟩ := exp_neg_enc (b / 2) (by linarith) (by linarith)
  have hmono := ehs_anti u b hu0 hu2
  have hd : 0 < Real.exp (b / 2) - Real.exp (-(3 * b / 2)) := by
    rw [sub_pos, Real.exp_lt_exp]; linarith
  have hfrac : 2 / ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 +
          (b / 2) ^ 5 / 100) -
        (1 - 3 * b / 2 + (3 * b / 2) ^ 2 / 2 - (3 * b / 2) ^ 3 / 6 + (3 * b / 2) ^ 4 / 24 -
          (3 * b / 2) ^ 5 / 100)) ≤ 2 / (Real.exp (b / 2) - Real.exp (-(3 * b / 2))) := by
    apply div_le_div_of_nonneg_left (by norm_num) hd
    linarith
  have hcosh : Real.cosh (u / 2) ≤ Real.cosh (b / 2) := by
    rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have hcb : 2 * Real.cosh (b / 2) ≤
      (1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) +
        (1 - b / 2 + (b / 2) ^ 2 / 2 - (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) := by
    rw [Real.cosh_eq]; linarith
  have hk : min (A + θa * (B - A)) (A + θb * (B - A)) ≤ hatK h n v u := by
    have e1 : ((k : ℝ) + θa) * h = k * h + θa * h := by ring
    have e2 : ((k : ℝ) + θb) * h = k * h + θb * h := by ring
    have e3 : ((k : ℝ) + 1) * h = k * h + 1 * h := by ring
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

/-- `cothTail x ≥ (k log 2 + 1 − 2^k / L^p)/p` from a lower bound on `e^{-x}`. -/
theorem cT_lower (x yl : ℝ) (p k : ℕ) (hx : 0 < x) (hyl : yl ≤ Real.exp (-x)) (hyl0 : 0 ≤ yl)
    (hp : 0 < p) (hk : (2 : ℝ) ^ k ≤ ((1 + yl) / (1 - yl)) ^ p) :
    ((k : ℝ) * Real.log 2 + 1 - 2 ^ k / ((1 + yl) / (1 - yl)) ^ p) / p ≤ cothTail x := by
  have he1 : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hyl1 : yl < 1 := lt_of_le_of_lt hyl he1
  set L := (1 + yl) / (1 - yl) with hL
  have hL0 : 0 < L := div_pos (by linarith) (by linarith)
  have hLY : L ≤ (1 + Real.exp (-x)) / (1 - Real.exp (-x)) := by
    rw [hL, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hlogL : Real.log L ≤ cothTail x := by
    unfold cothTail
    exact Real.log_le_log hL0 hLY
  have hLp : 0 < L ^ p := pow_pos hL0 p
  have hq : 0 < L ^ p / 2 ^ k := div_pos hLp (by positivity)
  have hlogq := Real.one_sub_inv_le_log_of_pos hq
  have hsplit : (p : ℝ) * Real.log L = k * Real.log 2 + Real.log (L ^ p / 2 ^ k) := by
    rw [Real.log_div hLp.ne' (by positivity), Real.log_pow, Real.log_pow]; ring
  have hinv : (L ^ p / 2 ^ k)⁻¹ = 2 ^ k / L ^ p := by rw [inv_div]
  rw [hinv] at hlogq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hpR]
  nlinarith

theorem sinh_lower (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x + x ^ 3 / 6 - x ^ 5 / 100 ≤ Real.sinh x := by
  obtain ⟨hp, -⟩ := exp_pos_enc x hx0 hx1
  obtain ⟨-, hn⟩ := exp_neg_enc x hx0 hx1
  rw [Real.sinh_eq]; linarith

/-- The rational check for one sub-cell with right endpoint `b`. -/
def checkF (lam σ A B θa θb b : ℝ) : ℝ :=
  2 / ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) -
      (1 - 3 * b / 2 + (3 * b / 2) ^ 2 / 2 - (3 * b / 2) ^ 3 / 6 + (3 * b / 2) ^ 4 / 24 -
        (3 * b / 2) ^ 5 / 100)) -
    lam * ((1 + b / 2 + (b / 2) ^ 2 / 2 + (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100) +
      (1 - b / 2 + (b / 2) ^ 2 / 2 - (b / 2) ^ 3 / 6 + (b / 2) ^ 4 / 24 + (b / 2) ^ 5 / 100)) +
    σ * min (A + θa * (B - A)) (A + θb * (B - A))

/-- **Sub-cell checks imply the kernel condition on `(0, Nh]`.** -/
theorem Q_of_checks (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (N s : ℕ) (rv : ℕ → ℝ) (hh : 0 < h)
    (hσ : 0 ≤ σ) (hl : 0 ≤ lam) (hs : 0 < s) (hNh : (N : ℝ) * h ≤ 2 / 3)
    (hnode : ∀ k : ℕ, k ≤ N → hatK h n v ((k : ℝ) * h) = h * rv k)
    (hcheck : ∀ m : ℕ, m < N * s → 0 ≤ checkF lam σ (h * rv (m / s)) (h * rv (m / s + 1))
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
  apply cell_Q lam σ h n v k ((j : ℝ) / s) (((j + 1 : ℕ) : ℝ) / s) (h * rv k) (h * rv (k + 1))
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

end AEGIS.RHHatCellsV13
