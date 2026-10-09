import RHHalfCapV13
import Mathlib.Tactic

/-!
AEGIS Ω — the three-cell cap for narrow autocorrelations, V13.

If the logarithmic lift `f` of `g` is supported in `[a − r, a + r]` and the shift `u`
satisfies `2r < 3u`, cut the line at `p = a − r + u` and `q = a − r + 2u`.  A pair
`(v, v + u)` with both points in the support lies either in `(I₀, I₁)` or in `(I₁, I₂)`,
where `I₀ = (−∞, p)`, `I₁ = [p, q)`, `I₂ = [q, ∞)`.  Weighted AM–GM with weights
`50/71` on the outer cells and `71/200` on the middle cell (their product is `1/4`) gives

  ‖logCorrelation g u‖ ≤ (50/71)·(E₀ + E₂) + (71/100)·E₁ ≤ (71/100)·E,

since `50/71 ≤ 71/100`.  This is the three-cell (`n = 1`) Boas–Kac case; the half-cap
`RHHalfCapV13` is the two-cell case.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHThreeCellV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.RHDyadicDiagonalV13

/-- **Three-cell cap.** -/
theorem three_cell_logCorrelation (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < 3 * u) (hu0 : 0 < u) :
    ‖logCorrelationV25 g u‖ ≤ (71 / 100) * energy g.1 := by
  set f : ℝ → ℂ := logLift g.1 with hf
  set F : ℝ → ℝ := fun w => ‖f w‖ ^ 2 with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => sq_nonneg _
  have hFi : Integrable F := logLift_sq_integrable_v25 g
  set p := a - r + u with hp
  set q := a - r + 2 * u with hq
  have hpq : p ≤ q := by linarith
  let q' : ℝ → ℂ := fun v => f (v + u) * conj (f v)
  let M : ℝ → ℝ := fun v =>
    (50 / 71 : ℝ) * (Iio p).indicator F v + (71 / 200 : ℝ) * (Ico p q).indicator F (v + u)
      + (71 / 200 : ℝ) * (Ico p q).indicator F v + (50 / 71 : ℝ) * (Ici q).indicator F (v + u)
  have hq' : Integrable q' := by simpa [q', f] using logCorrelation_integrable_v25 g u
  have hJ0 : Integrable (fun v => (Iio p).indicator F v) := hFi.indicator measurableSet_Iio
  have hJ1 : Integrable (fun v => (Ico p q).indicator F (v + u)) :=
    (hFi.indicator measurableSet_Ico).comp_add_right u
  have hJ2 : Integrable (fun v => (Ico p q).indicator F v) := hFi.indicator measurableSet_Ico
  have hJ3 : Integrable (fun v => (Ici q).indicator F (v + u)) :=
    (hFi.indicator measurableSet_Ici).comp_add_right u
  have hM : Integrable M :=
    (((hJ0.const_mul _).add (hJ1.const_mul _)).add (hJ2.const_mul _)).add (hJ3.const_mul _)
  have hind : ∀ (S : Set ℝ) (w : ℝ), 0 ≤ S.indicator F w :=
    fun S w => Set.indicator_nonneg (fun x _ => hF0 x) w
  have hpoint : ∀ v : ℝ, ‖q' v‖ ≤ M v := by
    intro v
    have hMnn : 0 ≤ M v := by
      unfold M
      have := hind (Iio p) v; have := hind (Ico p q) (v + u)
      have := hind (Ico p q) v; have := hind (Ici q) (v + u)
      positivity
    by_cases h0 : f v = 0
    · have : ‖q' v‖ = 0 := by simp [q', h0]
      rw [this]; exact hMnn
    by_cases h1 : f (v + u) = 0
    · have : ‖q' v‖ = 0 := by simp [q', h1]
      rw [this]; exact hMnn
    have hv := hw (subset_tsupport _ h0)
    have hvu := hw (subset_tsupport _ h1)
    have hnq : ‖q' v‖ = ‖f (v + u)‖ * ‖f v‖ := by simp [q']
    rw [hnq]
    set x := ‖f (v + u)‖ with hx
    set y := ‖f v‖ with hy
    by_cases hvp : v < p
    · -- v ∈ I₀, v + u ∈ I₁
      have hA : v ∈ Iio p := hvp
      have hB : v + u ∈ Ico p q := ⟨by linarith [hv.1], by linarith⟩
      have hvC : v ∉ Ico p q := fun h => absurd h.1 (not_le.mpr hvp)
      have hvuD : v + u ∉ Ici q := fun h => by
        change q ≤ v + u at h; linarith
      have hM' : M v = (50 / 71) * y ^ 2 + (71 / 200) * x ^ 2 := by
        unfold M
        rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB, Set.indicator_of_notMem hvC,
          Set.indicator_of_notMem hvuD]
        simp [F, hx, hy]
      rw [hM']
      nlinarith [sq_nonneg (y - (71 / 100) * x)]
    · -- v ∈ I₁, v + u ∈ I₂
      have hvp' : p ≤ v := not_lt.mp hvp
      have hvq : v < q := by linarith [hvu.2]
      have hA : v ∉ Iio p := fun h => hvp h
      have hB : v + u ∉ Ico p q := fun h => by linarith [h.2]
      have hC : v ∈ Ico p q := ⟨hvp', hvq⟩
      have hD : v + u ∈ Ici q := by change q ≤ v + u; linarith
      have hM' : M v = (71 / 200) * y ^ 2 + (50 / 71) * x ^ 2 := by
        unfold M
        rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, Set.indicator_of_mem hC,
          Set.indicator_of_mem hD]
        simp [F, hx, hy]
      rw [hM']
      nlinarith [sq_nonneg (x - (71 / 100) * y)]
  -- integrate
  have hsh1 : (∫ v : ℝ, (Ico p q).indicator F (v + u)) = ∫ w : ℝ, (Ico p q).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p q).indicator F w) u
  have hsh3 : (∫ v : ℝ, (Ici q).indicator F (v + u)) = ∫ w : ℝ, (Ici q).indicator F w :=
    integral_add_right_eq_self (fun w => (Ici q).indicator F w) u
  have hK2 : Integrable (fun w => (Ici q).indicator F w) := hFi.indicator measurableSet_Ici
  have hsplit : (∫ w : ℝ, (Iio p).indicator F w) + (∫ w : ℝ, (Ico p q).indicator F w)
      + (∫ w : ℝ, (Ici q).indicator F w) = ∫ w : ℝ, F w := by
    have hJ02 : Integrable (fun w => (Iio p).indicator F w + (Ico p q).indicator F w) :=
      hJ0.add hJ2
    rw [← integral_add hJ0 hJ2, ← integral_add hJ02 hK2]
    congr 1
    funext w
    by_cases h1 : w < p
    · have : w ∉ Ico p q := fun h => absurd h.1 (not_le.mpr h1)
      have h2 : w ∉ Ici q := fun h => by change q ≤ w at h; linarith
      simp [Set.indicator_of_mem (show w ∈ Iio p from h1), Set.indicator_of_notMem this,
        Set.indicator_of_notMem h2]
    · by_cases h3 : w < q
      · have hA : w ∉ Iio p := h1
        have hC : w ∈ Ico p q := ⟨not_lt.mp h1, h3⟩
        have hD : w ∉ Ici q := fun h => by change q ≤ w at h; linarith
        simp [Set.indicator_of_notMem hA, Set.indicator_of_mem hC, Set.indicator_of_notMem hD]
      · have hA : w ∉ Iio p := h1
        have hC : w ∉ Ico p q := fun h => h3 h.2
        have hD : w ∈ Ici q := not_lt.mp h3
        simp [Set.indicator_of_notMem hA, Set.indicator_of_notMem hC, Set.indicator_of_mem hD]
  have hE : (∫ w : ℝ, F w) = energy g.1 := by
    simpa [F, f] using logLift_energy_eq_packet_energy g
  have hI0 : 0 ≤ ∫ w : ℝ, (Iio p).indicator F w := integral_nonneg (fun w => hind (Iio p) w)
  have hI1 : 0 ≤ ∫ w : ℝ, (Ico p q).indicator F w := integral_nonneg (fun w => hind (Ico p q) w)
  have hI2 : 0 ≤ ∫ w : ℝ, (Ici q).indicator F w := integral_nonneg (fun w => hind (Ici q) w)
  calc
    ‖logCorrelationV25 g u‖ = ‖∫ v : ℝ, q' v‖ := by rfl
    _ ≤ ∫ v : ℝ, ‖q' v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hq'.norm hM hpoint
    _ = (50 / 71) * (∫ v : ℝ, (Iio p).indicator F v)
          + (71 / 200) * (∫ v : ℝ, (Ico p q).indicator F (v + u))
          + (71 / 200) * (∫ v : ℝ, (Ico p q).indicator F v)
          + (50 / 71) * (∫ v : ℝ, (Ici q).indicator F (v + u)) := by
      have hA0 : Integrable (fun v => (50 / 71 : ℝ) * (Iio p).indicator F v) := hJ0.const_mul _
      have hA1 : Integrable (fun v => (71 / 200 : ℝ) * (Ico p q).indicator F (v + u)) :=
        hJ1.const_mul _
      have hA2 : Integrable (fun v => (71 / 200 : ℝ) * (Ico p q).indicator F v) := hJ2.const_mul _
      have hA3 : Integrable (fun v => (50 / 71 : ℝ) * (Ici q).indicator F (v + u)) :=
        hJ3.const_mul _
      have h01 : Integrable (fun v => (50 / 71 : ℝ) * (Iio p).indicator F v
          + (71 / 200 : ℝ) * (Ico p q).indicator F (v + u)) := hA0.add hA1
      have h012 : Integrable (fun v => (50 / 71 : ℝ) * (Iio p).indicator F v
          + (71 / 200 : ℝ) * (Ico p q).indicator F (v + u)
          + (71 / 200 : ℝ) * (Ico p q).indicator F v) := h01.add hA2
      unfold M
      rw [integral_add h012 hA3, integral_add h01 hA2, integral_add hA0 hA1,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ (71 / 100) * energy g.1 := by
      rw [hsh1, hsh3, ← hE, ← hsplit]
      nlinarith

/-- Two-sided exponential form: for `2r < 3u`,
`|e^u · Re A(e^u)| ≤ (71/100)·e^{u/2}·E`. -/
theorem three_cell_exp_re_bounds (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < 3 * u) (hu0 : 0 < u) :
    -(Real.exp (u / 2) * ((71 / 100) * energy g.1)) ≤
        Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re ∧
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re ≤
        Real.exp (u / 2) * ((71 / 100) * energy g.1) := by
  have h := three_cell_logCorrelation g r a u hw hu hu0
  rw [logCorrelation_eq_autocorrelation_v25] at h
  have hnorm : Real.exp (u / 2) * ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
      (71 / 100) * energy g.1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h
  have hsplit : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he := Real.exp_pos (u / 2)
  set N := ‖WeilAutocorrelationV1 g (Real.exp u)‖ with hN
  have hre1 : -N ≤ (WeilAutocorrelationV1 g (Real.exp u)).re :=
    le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
  have hre2 : (WeilAutocorrelationV1 g (Real.exp u)).re ≤ N :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have h2 : Real.exp u * N ≤ Real.exp (u / 2) * ((71 / 100) * energy g.1) := by
    have hmul := mul_le_mul_of_nonneg_left hnorm he.le
    have heq : Real.exp u * N = Real.exp (u / 2) * (Real.exp (u / 2) * N) := by
      rw [← mul_assoc, ← hsplit]
    rw [heq]; exact hmul
  have hp := Real.exp_pos u
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hre1 hp.le]
  · nlinarith [mul_le_mul_of_nonneg_left hre2 hp.le]

end AEGIS.RHThreeCellV13

#print axioms AEGIS.RHThreeCellV13.three_cell_logCorrelation
#print axioms AEGIS.RHThreeCellV13.three_cell_exp_re_bounds
