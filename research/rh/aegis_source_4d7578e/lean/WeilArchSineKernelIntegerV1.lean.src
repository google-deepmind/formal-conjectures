import WeilArchSineKernelV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
AEGIS Ω — integer-node closed forms for the true Archimedean sine source.

This child module leaves the already-verified differentiation-under-integral
bridge unchanged and proves only the two nonresonant integer-node formulas
needed before the Cauchy rank-two identification.

No Cauchy--Stieltjes integration, PSD import, operator order, global Weil
positivity, formula-to-Weil identity, or RH claim is made.
-/

open intervalIntegral

set_option autoImplicit false

noncomputable section

private theorem integral_sin_linear_v1 (k L : ℝ) (hk : k ≠ 0) :
    (∫ y in (0 : ℝ)..L, Real.sin (k * y)) =
      (1 - Real.cos (k * L)) / k := by
  have hscale :
      k * (∫ y in (0 : ℝ)..L, Real.sin (k * y)) =
        1 - Real.cos (k * L) := by
    calc
      k * (∫ y in (0 : ℝ)..L, Real.sin (k * y)) =
          ∫ y in k * 0..k * L, Real.sin y := by
            simpa using
              (intervalIntegral.mul_integral_comp_mul_left
                (a := (0 : ℝ)) (b := L) (f := Real.sin) k)
      _ = 1 - Real.cos (k * L) := by simp
  apply (eq_div_iff hk).2
  simpa [mul_comm] using hscale

private theorem integral_sin_mul_cos_linear_v1
    (A T L : ℝ) (hsub : A - T ≠ 0) (hadd : A + T ≠ 0) :
    (∫ y in (0 : ℝ)..L, Real.sin (A * y) * Real.cos (T * y)) =
      (1 / 2 : ℝ) *
        ((1 - Real.cos ((A - T) * L)) / (A - T) +
          (1 - Real.cos ((A + T) * L)) / (A + T)) := by
  have hfun :
      (fun y : ℝ => Real.sin (A * y) * Real.cos (T * y)) =
        fun y : ℝ => (1 / 2 : ℝ) *
          (Real.sin ((A - T) * y) + Real.sin ((A + T) * y)) := by
    funext y
    have htrig := Real.two_mul_sin_mul_cos (A * y) (T * y)
    rw [show A * y - T * y = (A - T) * y by ring,
      show A * y + T * y = (A + T) * y by ring] at htrig
    linarith
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun y : ℝ => Real.sin ((A - T) * y))).intervalIntegrable 0 L)
    ((by fun_prop : Continuous (fun y : ℝ => Real.sin ((A + T) * y))).intervalIntegrable 0 L)]
  rw [integral_sin_linear_v1 (A - T) L hsub,
    integral_sin_linear_v1 (A + T) L hadd]

private theorem integral_weighted_cos_linear_v1
    (L k : ℝ) (hL : L ≠ 0) (hk : k ≠ 0) :
    (∫ y in (0 : ℝ)..L, (1 - y / L) * Real.cos (k * y)) =
      (1 - Real.cos (k * L)) / (L * k ^ 2) := by
  let u : ℝ → ℝ := fun y => 1 - y / L
  let u' : ℝ → ℝ := fun _ => -(1 / L)
  let v : ℝ → ℝ := fun y => Real.sin (k * y) / k
  let v' : ℝ → ℝ := fun y => Real.cos (k * y)
  have hu : ∀ y ∈ Set.uIcc (0 : ℝ) L, HasDerivAt u (u' y) y := by
    intro y hy
    dsimp [u, u']
    have hbase :=
      (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).div_const L)
    have hfun :
        ((fun _ : ℝ => (1 : ℝ)) - fun z : ℝ => id z / L) =
          (fun z : ℝ => 1 - z / L) := by
      funext z
      rfl
    rw [hfun] at hbase
    simpa only [zero_sub] using hbase
  have hv : ∀ y ∈ Set.uIcc (0 : ℝ) L, HasDerivAt v (v' y) y := by
    intro y hy
    dsimp [v, v']
    have hlin : HasDerivAt (fun z : ℝ => k * z) k y := by
      simpa using (hasDerivAt_id y).const_mul k
    have hsin := (Real.hasDerivAt_sin (k * y)).comp y hlin
    have hdiv := hsin.div_const k
    refine hdiv.congr_deriv ?_
    field_simp [hk]
  have hu_int : IntervalIntegrable u' MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hv_int : IntervalIntegrable v' MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu_int hv_int
  have huL : u L = 0 := by
    simp [u, hL]
  have hu0 : u 0 = 1 := by simp [u]
  have hv0 : v 0 = 0 := by simp [v]
  have hconst :
      (fun y : ℝ => u' y * v y) =
        fun y : ℝ => (-1 / (L * k)) * Real.sin (k * y) := by
    funext y
    dsimp [u', v]
    field_simp [hL, hk] <;> ring
  calc
    (∫ y in (0 : ℝ)..L, (1 - y / L) * Real.cos (k * y)) =
        u L * v L - u 0 * v 0 - ∫ y in (0 : ℝ)..L, u' y * v y := by
          simpa [u, v'] using hibp
    _ = - ∫ y in (0 : ℝ)..L, (-1 / (L * k)) * Real.sin (k * y) := by
          rw [huL, hu0, hv0, hconst]
          simp
    _ = (1 / (L * k)) * (∫ y in (0 : ℝ)..L, Real.sin (k * y)) := by
          rw [intervalIntegral.integral_const_mul]
          ring
    _ = (1 - Real.cos (k * L)) / (L * k ^ 2) := by
          rw [integral_sin_linear_v1 k L hk]
          field_simp [hL, hk] <;> ring

private theorem integral_weighted_cos_mul_cos_linear_v1
    (L A T : ℝ) (hL : L ≠ 0)
    (hsub : A - T ≠ 0) (hadd : A + T ≠ 0) :
    (∫ y in (0 : ℝ)..L,
      (1 - y / L) * Real.cos (A * y) * Real.cos (T * y)) =
      (1 / 2 : ℝ) *
        ((1 - Real.cos ((A - T) * L)) / (L * (A - T) ^ 2) +
          (1 - Real.cos ((A + T) * L)) / (L * (A + T) ^ 2)) := by
  have hfun :
      (fun y : ℝ => (1 - y / L) * Real.cos (A * y) * Real.cos (T * y)) =
        fun y : ℝ => (1 / 2 : ℝ) *
          ((1 - y / L) * Real.cos ((A - T) * y) +
            (1 - y / L) * Real.cos ((A + T) * y)) := by
    funext y
    have htrig := Real.two_mul_cos_mul_cos (A * y) (T * y)
    rw [show A * y - T * y = (A - T) * y by ring,
      show A * y + T * y = (A + T) * y by ring] at htrig
    linear_combination (1 - y / L) / 2 * htrig
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun y : ℝ =>
      (1 - y / L) * Real.cos ((A - T) * y))).intervalIntegrable 0 L)
    ((by fun_prop : Continuous (fun y : ℝ =>
      (1 - y / L) * Real.cos ((A + T) * y))).intervalIntegrable 0 L)]
  rw [integral_weighted_cos_linear_v1 L (A - T) hL hsub,
    integral_weighted_cos_linear_v1 L (A + T) hL hadd]

private theorem arch_sin_phase_integer_v1 (L y : ℝ) (n : ℤ) :
    Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
      -Real.sin (WeilArchRhoV1 L * (n : ℝ) * y) := by
  calc
    Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
        Real.sin ((n : ℝ) * (2 * Real.pi) -
          2 * Real.pi * (y / L) * (n : ℝ)) := by
            congr 1
            ring
    _ = -Real.sin (2 * Real.pi * (y / L) * (n : ℝ)) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            Real.sin_int_mul_two_pi_sub
              (2 * Real.pi * (y / L) * (n : ℝ)) n
    _ = -Real.sin (WeilArchRhoV1 L * (n : ℝ) * y) := by
          congr 1
          simp [WeilArchRhoV1]
          ring

private theorem arch_cos_phase_integer_v1 (L y : ℝ) (n : ℤ) :
    Real.cos (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
      Real.cos (WeilArchRhoV1 L * (n : ℝ) * y) := by
  calc
    Real.cos (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
        Real.cos ((n : ℝ) * (2 * Real.pi) -
          2 * Real.pi * (y / L) * (n : ℝ)) := by
            congr 1
            ring
    _ = Real.cos (2 * Real.pi * (y / L) * (n : ℝ)) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            Real.cos_int_mul_two_pi_sub
              (2 * Real.pi * (y / L) * (n : ℝ)) n
    _ = Real.cos (WeilArchRhoV1 L * (n : ℝ) * y) := by
          congr 1
          simp [WeilArchRhoV1]
          ring

private theorem one_sub_cos_eq_two_sin_sq_half_v1 (z : ℝ) :
    1 - Real.cos z = 2 * Real.sin (z / 2) ^ 2 := by
  have hcos :
      Real.cos z = Real.cos (z / 2) ^ 2 - Real.sin (z / 2) ^ 2 := by
    convert Real.cos_two_mul' (z / 2) using 1 <;> ring
  rw [hcos]
  nlinarith [Real.sin_sq_add_cos_sq (z / 2)]

private theorem inv_sub_add_inv_add_v1
    (A T : ℝ) (hsub : A - T ≠ 0) (hadd : A + T ≠ 0)
    (hden : T ^ 2 - A ^ 2 ≠ 0) :
    1 / (A - T) + 1 / (A + T) = -2 * A / (T ^ 2 - A ^ 2) := by
  field_simp [hsub, hadd, hden]
  ring

private theorem inv_sq_sub_add_inv_sq_add_v1
    (A T : ℝ) (hsub : A - T ≠ 0) (hadd : A + T ≠ 0)
    (hden : T ^ 2 - A ^ 2 ≠ 0) :
    1 / (A - T) ^ 2 + 1 / (A + T) ^ 2 =
      2 * (T ^ 2 + A ^ 2) / (T ^ 2 - A ^ 2) ^ 2 := by
  field_simp [hsub, hadd, hden]
  ring

/-- Exact integer-node evaluation of the Archimedean sine kernel away from
its two resonant denominators. -/
theorem weil_arch_sine_kernel_integer_v1
    (L T : ℝ) (n : ℤ) (hL : L ≠ 0)
    (hden : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchSineKernelV1 L T (n : ℝ) =
      2 * WeilArchRhoV1 L * (n : ℝ) * Real.sin (L * T / 2) ^ 2 /
        (T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2) := by
  let A : ℝ := WeilArchRhoV1 L * (n : ℝ)
  have hdenA : T ^ 2 - A ^ 2 ≠ 0 := by simpa [A] using hden
  have hsub : A - T ≠ 0 := by
    intro h
    apply hdenA
    have hAT : A = T := sub_eq_zero.mp h
    rw [hAT]
    ring
  have hadd : A + T ≠ 0 := by
    intro h
    apply hdenA
    have hAT : A = -T := by linarith
    rw [hAT]
    ring
  have hAL : A * L = (n : ℝ) * (2 * Real.pi) := by
    dsimp [A, WeilArchRhoV1]
    field_simp [hL] <;> ring
  have hphase_sub : (A - T) * L = (n : ℝ) * (2 * Real.pi) - T * L := by
    calc
      (A - T) * L = A * L - T * L := by ring
      _ = (n : ℝ) * (2 * Real.pi) - T * L := by rw [hAL]
  have hphase_add : (A + T) * L = T * L + (n : ℝ) * (2 * Real.pi) := by
    calc
      (A + T) * L = A * L + T * L := by ring
      _ = T * L + (n : ℝ) * (2 * Real.pi) := by rw [hAL]; ring
  have hcos_sub : Real.cos ((A - T) * L) = Real.cos (T * L) := by
    rw [hphase_sub]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Real.cos_int_mul_two_pi_sub (T * L) n
  have hcos_add : Real.cos ((A + T) * L) = Real.cos (T * L) := by
    rw [hphase_add]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Real.cos_add_int_mul_two_pi (T * L) n
  have hhalf : 1 - Real.cos (T * L) = 2 * Real.sin (L * T / 2) ^ 2 := by
    rw [show T * L = L * T by ring]
    exact one_sub_cos_eq_two_sin_sq_half_v1 (L * T)
  have hinv := inv_sub_add_inv_add_v1 A T hsub hadd hdenA
  unfold WeilArchSineKernelV1
  have hfun :
      (fun y : ℝ =>
        Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) * Real.cos (T * y)) =
      (fun y : ℝ => -(Real.sin (A * y) * Real.cos (T * y))) := by
    funext y
    rw [arch_sin_phase_integer_v1]
    dsimp [A]
    ring
  rw [hfun, intervalIntegral.integral_neg]
  rw [integral_sin_mul_cos_linear_v1 A T L hsub hadd]
  rw [hcos_sub, hcos_add, hhalf]
  calc
    -(1 / 2 *
      ((2 * Real.sin (L * T / 2) ^ 2) / (A - T) +
        (2 * Real.sin (L * T / 2) ^ 2) / (A + T))) =
        -Real.sin (L * T / 2) ^ 2 *
          (1 / (A - T) + 1 / (A + T)) := by ring
    _ = 2 * A * Real.sin (L * T / 2) ^ 2 / (T ^ 2 - A ^ 2) := by
      rw [hinv]
      simp only [div_eq_mul_inv]
      ring
    _ = 2 * WeilArchRhoV1 L * (n : ℝ) * Real.sin (L * T / 2) ^ 2 /
        (T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2) := by
      simp [A, mul_assoc]

/-- Exact integer-node value of the true x-derivative of the Archimedean sine
kernel, again away from the resonant denominators. -/
theorem weil_arch_sine_kernel_dx_integer_v1
    (L T : ℝ) (n : ℤ) (hL : L ≠ 0)
    (hden : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchSineKernelDxV1 L T (n : ℝ) =
      2 * WeilArchRhoV1 L * Real.sin (L * T / 2) ^ 2 *
        (T ^ 2 + (WeilArchRhoV1 L * (n : ℝ)) ^ 2) /
        (T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2) ^ 2 := by
  let A : ℝ := WeilArchRhoV1 L * (n : ℝ)
  have hdenA : T ^ 2 - A ^ 2 ≠ 0 := by simpa [A] using hden
  have hsub : A - T ≠ 0 := by
    intro h
    apply hdenA
    have hAT : A = T := sub_eq_zero.mp h
    rw [hAT]
    ring
  have hadd : A + T ≠ 0 := by
    intro h
    apply hdenA
    have hAT : A = -T := by linarith
    rw [hAT]
    ring
  have hAL : A * L = (n : ℝ) * (2 * Real.pi) := by
    dsimp [A, WeilArchRhoV1]
    field_simp [hL] <;> ring
  have hphase_sub : (A - T) * L = (n : ℝ) * (2 * Real.pi) - T * L := by
    calc
      (A - T) * L = A * L - T * L := by ring
      _ = (n : ℝ) * (2 * Real.pi) - T * L := by rw [hAL]
  have hphase_add : (A + T) * L = T * L + (n : ℝ) * (2 * Real.pi) := by
    calc
      (A + T) * L = A * L + T * L := by ring
      _ = T * L + (n : ℝ) * (2 * Real.pi) := by rw [hAL]; ring
  have hcos_sub : Real.cos ((A - T) * L) = Real.cos (T * L) := by
    rw [hphase_sub]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Real.cos_int_mul_two_pi_sub (T * L) n
  have hcos_add : Real.cos ((A + T) * L) = Real.cos (T * L) := by
    rw [hphase_add]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Real.cos_add_int_mul_two_pi (T * L) n
  have hhalf : 1 - Real.cos (T * L) = 2 * Real.sin (L * T / 2) ^ 2 := by
    rw [show T * L = L * T by ring]
    exact one_sub_cos_eq_two_sin_sq_half_v1 (L * T)
  have hinv2 := inv_sq_sub_add_inv_sq_add_v1 A T hsub hadd hdenA
  unfold WeilArchSineKernelDxV1
  have hfun :
      (fun y : ℝ =>
        (2 * Real.pi * (1 - y / L) *
          Real.cos (2 * Real.pi * (n : ℝ) * (1 - y / L))) * Real.cos (T * y)) =
      (fun y : ℝ =>
        (2 * Real.pi) * ((1 - y / L) * Real.cos (A * y) * Real.cos (T * y))) := by
    funext y
    rw [arch_cos_phase_integer_v1]
    dsimp [A]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [integral_weighted_cos_mul_cos_linear_v1 L A T hL hsub hadd]
  rw [hcos_sub, hcos_add, hhalf]
  calc
    (2 * Real.pi) *
      (1 / 2 *
        ((2 * Real.sin (L * T / 2) ^ 2) / (L * (A - T) ^ 2) +
          (2 * Real.sin (L * T / 2) ^ 2) / (L * (A + T) ^ 2))) =
        (2 * Real.pi / L) * Real.sin (L * T / 2) ^ 2 *
          (1 / (A - T) ^ 2 + 1 / (A + T) ^ 2) := by
      field_simp [hL, hsub, hadd]
    _ = (2 * Real.pi / L) * Real.sin (L * T / 2) ^ 2 *
        (2 * (T ^ 2 + A ^ 2) / (T ^ 2 - A ^ 2) ^ 2) := by rw [hinv2]
    _ = 2 * WeilArchRhoV1 L * Real.sin (L * T / 2) ^ 2 *
        (T ^ 2 + (WeilArchRhoV1 L * (n : ℝ)) ^ 2) /
        (T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2) ^ 2 := by
      have hAeq : WeilArchRhoV1 L * (n : ℝ) = A := rfl
      rw [hAeq]
      simp only [WeilArchRhoV1, div_eq_mul_inv]
      ring

#print axioms weil_arch_sine_kernel_integer_v1
#print axioms weil_arch_sine_kernel_dx_integer_v1


/-- Cauchy node associated with the Archimedean spectral parameter. -/
def WeilArchNodeV1 (L T : ℝ) : ℝ :=
  T / WeilArchRhoV1 L

/-- Scalar multiplying the rational Cauchy source core at integer nodes. -/
def WeilArchScaleV1 (L T : ℝ) : ℝ :=
  2 * Real.sin (L * T / 2) ^ 2 / WeilArchRhoV1 L

/-- The true Archimedean sine-source entry: derivative on the diagonal and
divided difference off the diagonal. -/
def WeilArchSineEntryV1 (L T : ℝ) (m n : ℤ) : ℝ :=
  if m = n then
    WeilArchSineKernelDxV1 L T (m : ℝ)
  else
    (WeilArchSineKernelV1 L T (m : ℝ) -
      WeilArchSineKernelV1 L T (n : ℝ)) /
      ((m : ℝ) - (n : ℝ))

private theorem weil_arch_rho_ne_zero_v1
    (L : ℝ) (hL : L ≠ 0) :
    WeilArchRhoV1 L ≠ 0 := by
  unfold WeilArchRhoV1
  exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL

private theorem weil_arch_node_sq_sub_ne_zero_v1
    (L T : ℝ) (n : ℤ) (hL : L ≠ 0)
    (hden : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchNodeV1 L T ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
  have hrho : WeilArchRhoV1 L ≠ 0 := weil_arch_rho_ne_zero_v1 L hL
  intro h
  apply hden
  have hscale :
      T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 =
        WeilArchRhoV1 L ^ 2 *
          (WeilArchNodeV1 L T ^ 2 - (n : ℝ) ^ 2) := by
    unfold WeilArchNodeV1
    field_simp [hrho]
  rw [hscale, h]
  ring

private theorem sub_ne_zero_of_sq_sub_sq_ne_zero_v1
    (a x : ℝ) (h : a ^ 2 - x ^ 2 ≠ 0) :
    a - x ≠ 0 := by
  intro hx
  apply h
  rw [show a ^ 2 - x ^ 2 = (a - x) * (a + x) by ring, hx]
  ring

private theorem add_ne_zero_of_sq_sub_sq_ne_zero_v1
    (a x : ℝ) (h : a ^ 2 - x ^ 2 ≠ 0) :
    a + x ≠ 0 := by
  intro hx
  apply h
  rw [show a ^ 2 - x ^ 2 = (a - x) * (a + x) by ring, hx]
  ring

private theorem weil_arch_sine_kernel_integer_core_v1
    (L T : ℝ) (n : ℤ) (hL : L ≠ 0)
    (hden : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchSineKernelV1 L T (n : ℝ) =
      WeilArchScaleV1 L T *
        WeilCauchySourceCoreV1 (WeilArchNodeV1 L T) (n : ℝ) := by
  have hrho : WeilArchRhoV1 L ≠ 0 := weil_arch_rho_ne_zero_v1 L hL
  have hcore :
      WeilArchNodeV1 L T ^ 2 - (n : ℝ) ^ 2 ≠ 0 :=
    weil_arch_node_sq_sub_ne_zero_v1 L T n hL hden
  rw [weil_arch_sine_kernel_integer_v1 L T n hL hden]
  simp only [WeilArchScaleV1, WeilArchNodeV1, WeilCauchySourceCoreV1]
  have hcore' :
      (T / WeilArchRhoV1 L) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    simpa [WeilArchNodeV1] using hcore
  field_simp [hrho, hden, hcore']

private theorem weil_arch_sine_kernel_dx_integer_core_v1
    (L T : ℝ) (n : ℤ) (hL : L ≠ 0)
    (hden : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchSineKernelDxV1 L T (n : ℝ) =
      WeilArchScaleV1 L T *
        WeilCauchyDiagonalV1 (WeilArchNodeV1 L T) (n : ℝ) := by
  have hrho : WeilArchRhoV1 L ≠ 0 := weil_arch_rho_ne_zero_v1 L hL
  have hcore :
      WeilArchNodeV1 L T ^ 2 - (n : ℝ) ^ 2 ≠ 0 :=
    weil_arch_node_sq_sub_ne_zero_v1 L T n hL hden
  rw [weil_arch_sine_kernel_dx_integer_v1 L T n hL hden]
  simp only [WeilArchScaleV1, WeilArchNodeV1, WeilCauchyDiagonalV1]
  have hcore' :
      (T / WeilArchRhoV1 L) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    simpa [WeilArchNodeV1] using hcore
  field_simp [hrho, hden, hcore']

/-- Exact pointwise Archimedean-to-Cauchy entry identification.  Away from the
two resonant denominators, the entry generated by the true sine source equals
one nonnegative-looking scalar factor times the rank-two Cauchy feature entry.
This theorem is an entry identity only: it does not integrate in T and does not
promote finite PSD, operator order, global Weil positivity, or RH. -/
theorem weil_arch_sine_entry_cauchy_rank_two_v1
    (L T : ℝ) (m n : ℤ) (hL : L ≠ 0)
    (hm : T ^ 2 - (WeilArchRhoV1 L * (m : ℝ)) ^ 2 ≠ 0)
    (hn : T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchSineEntryV1 L T m n =
      WeilArchScaleV1 L T *
        WeilCauchyRankTwoEntryV1
          (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ) := by
  by_cases hmn : m = n
  · subst n
    have hcore :
        WeilArchNodeV1 L T ^ 2 - (m : ℝ) ^ 2 ≠ 0 :=
      weil_arch_node_sq_sub_ne_zero_v1 L T m hL hm
    have hminus :
        WeilArchNodeV1 L T - (m : ℝ) ≠ 0 :=
      sub_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (m : ℝ) hcore
    have hplus :
        WeilArchNodeV1 L T + (m : ℝ) ≠ 0 :=
      add_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (m : ℝ) hcore
    rw [WeilArchSineEntryV1, if_pos rfl]
    rw [weil_arch_sine_kernel_dx_integer_core_v1 L T m hL hm]
    rw [weil_cauchy_diagonal_rank_two_v1
      (WeilArchNodeV1 L T) (m : ℝ) hminus hplus]
  · have hmnR : (m : ℝ) ≠ (n : ℝ) := by exact_mod_cast hmn
    have hcorem :
        WeilArchNodeV1 L T ^ 2 - (m : ℝ) ^ 2 ≠ 0 :=
      weil_arch_node_sq_sub_ne_zero_v1 L T m hL hm
    have hcoren :
        WeilArchNodeV1 L T ^ 2 - (n : ℝ) ^ 2 ≠ 0 :=
      weil_arch_node_sq_sub_ne_zero_v1 L T n hL hn
    have hmm :
        WeilArchNodeV1 L T - (m : ℝ) ≠ 0 :=
      sub_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (m : ℝ) hcorem
    have hpm :
        WeilArchNodeV1 L T + (m : ℝ) ≠ 0 :=
      add_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (m : ℝ) hcorem
    have hmn' :
        WeilArchNodeV1 L T - (n : ℝ) ≠ 0 :=
      sub_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (n : ℝ) hcoren
    have hpn :
        WeilArchNodeV1 L T + (n : ℝ) ≠ 0 :=
      add_ne_zero_of_sq_sub_sq_ne_zero_v1
        (WeilArchNodeV1 L T) (n : ℝ) hcoren
    rw [WeilArchSineEntryV1, if_neg hmn]
    rw [weil_arch_sine_kernel_integer_core_v1 L T m hL hm,
      weil_arch_sine_kernel_integer_core_v1 L T n hL hn]
    calc
      (WeilArchScaleV1 L T *
          WeilCauchySourceCoreV1 (WeilArchNodeV1 L T) (m : ℝ) -
        WeilArchScaleV1 L T *
          WeilCauchySourceCoreV1 (WeilArchNodeV1 L T) (n : ℝ)) /
          ((m : ℝ) - (n : ℝ)) =
        WeilArchScaleV1 L T *
          ((WeilCauchySourceCoreV1 (WeilArchNodeV1 L T) (m : ℝ) -
            WeilCauchySourceCoreV1 (WeilArchNodeV1 L T) (n : ℝ)) /
            ((m : ℝ) - (n : ℝ))) := by ring
      _ = WeilArchScaleV1 L T *
          WeilCauchyRankTwoEntryV1
            (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ) := by
        rw [weil_cauchy_divided_difference_rank_two_v1
          (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ)
          hmm hpm hmn' hpn hmnR]

#print axioms weil_arch_sine_entry_cauchy_rank_two_v1


/-- Finite quadratic contraction of the true Archimedean sine-source entry at
one fixed spectral parameter T. -/
def WeilArchFiniteQuadraticV1
    (I : Finset ℤ) (L T : ℝ) (u : ℤ → ℝ) : ℝ :=
  ∑ m ∈ I, ∑ n ∈ I,
    u m * u n * WeilArchSineEntryV1 L T m n

/-- At a fixed nonresonant T, the finite Archimedean quadratic is exactly the
common scalar factor times the real rank-two Cauchy Gram quadratic. -/
theorem weil_arch_finite_quadratic_scaled_cauchy_v1
    (I : Finset ℤ) (L T : ℝ) (u : ℤ → ℝ)
    (hL : L ≠ 0)
    (hden : ∀ n ∈ I,
      T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    WeilArchFiniteQuadraticV1 I L T u =
      WeilArchScaleV1 L T *
        WeilCauchyFiniteQuadraticV1 I (WeilArchNodeV1 L T)
          (fun n : ℤ => (n : ℝ)) u := by
  unfold WeilArchFiniteQuadraticV1 WeilCauchyFiniteQuadraticV1
  calc
    (∑ m ∈ I, ∑ n ∈ I,
      u m * u n * WeilArchSineEntryV1 L T m n) =
        ∑ m ∈ I, ∑ n ∈ I,
          u m * u n *
            (WeilArchScaleV1 L T *
              WeilCauchyRankTwoEntryV1
                (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m hmI
          apply Finset.sum_congr rfl
          intro n hnI
          rw [weil_arch_sine_entry_cauchy_rank_two_v1
            L T m n hL (hden m hmI) (hden n hnI)]
    _ = ∑ m ∈ I, ∑ n ∈ I,
          WeilArchScaleV1 L T *
            (u m * u n *
              WeilCauchyRankTwoEntryV1
                (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m hmI
          apply Finset.sum_congr rfl
          intro n hnI
          ring
    _ = WeilArchScaleV1 L T *
          (∑ m ∈ I, ∑ n ∈ I,
            u m * u n *
              WeilCauchyRankTwoEntryV1
                (WeilArchNodeV1 L T) (m : ℝ) (n : ℝ)) := by
          simp_rw [← Finset.mul_sum]

/-- For positive L, the scalar multiplying the Cauchy Gram kernel is
nonnegative. -/
theorem weil_arch_scale_nonnegative_v1
    (L T : ℝ) (hL : 0 < L) :
    0 ≤ WeilArchScaleV1 L T := by
  have hrho : 0 < WeilArchRhoV1 L := by
    unfold WeilArchRhoV1
    positivity
  unfold WeilArchScaleV1
  exact div_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg (Real.sin (L * T / 2))))
    (le_of_lt hrho)

/-- Fixed-T finite-band Archimedean Gram positivity.  This is pointwise in T;
it does not establish the subsequent continuous T-integral/operator-order
statement. -/
theorem weil_arch_finite_quadratic_nonnegative_v1
    (I : Finset ℤ) (L T : ℝ) (u : ℤ → ℝ)
    (hL : 0 < L)
    (hden : ∀ n ∈ I,
      T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    0 ≤ WeilArchFiniteQuadraticV1 I L T u := by
  rw [weil_arch_finite_quadratic_scaled_cauchy_v1
    I L T u (ne_of_gt hL) hden]
  exact mul_nonneg
    (weil_arch_scale_nonnegative_v1 L T hL)
    (weil_cauchy_finite_quadratic_nonnegative_v1
      I (WeilArchNodeV1 L T) (fun n : ℤ => (n : ℝ)) u)

/-- Compatibility name emphasizing the sine-source origin of the fixed-T
quadratic. -/
theorem weil_arch_sine_finite_quadratic_nonnegative_v1
    (I : Finset ℤ) (L T : ℝ) (u : ℤ → ℝ)
    (hL : 0 < L)
    (hden : ∀ n ∈ I,
      T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    0 ≤ WeilArchFiniteQuadraticV1 I L T u :=
  weil_arch_finite_quadratic_nonnegative_v1 I L T u hL hden

#print axioms weil_arch_finite_quadratic_scaled_cauchy_v1
#print axioms weil_arch_scale_nonnegative_v1
#print axioms weil_arch_finite_quadratic_nonnegative_v1
#print axioms weil_arch_sine_finite_quadratic_nonnegative_v1
