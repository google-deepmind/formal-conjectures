import RHThreeCellV13
import Mathlib.Tactic

/-!
AEGIS Ω — 7-cell Boas–Kac cap for narrow autocorrelations, V13.

If `2r < 7·u`, weighted AM–GM along the Coxeter–Dynkin path `A_7` gives
`‖logCorrelation g u‖ ≤ K·E` with `K = 93/100 ≥ cos(π/8)`.  Aggregated by `RHCellCapsV13`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCellCapsV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.RHDyadicDiagonalV13

set_option maxHeartbeats 4000000 in
/-- **7-cell cap** (`2r < 7u`): `‖logCorrelation g u‖ ≤ 93/100 · E`, with `93/100 ≥ cos(π/8)`. -/
theorem cell7_logCorrelation (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < 7 * u) (hu0 : 0 < u) :
    ‖logCorrelationV25 g u‖ ≤ (93 / 100 : ℝ) * energy g.1 := by
  set f : ℝ → ℂ := logLift g.1 with hf
  set F : ℝ → ℝ := fun w => ‖f w‖ ^ 2 with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => sq_nonneg _
  have hFi : Integrable F := logLift_sq_integrable_v25 g
  set p1 := a - r + 1 * u with hp1
  set p2 := a - r + 2 * u with hp2
  set p3 := a - r + 3 * u with hp3
  set p4 := a - r + 4 * u with hp4
  set p5 := a - r + 5 * u with hp5
  set p6 := a - r + 6 * u with hp6
  let q' : ℝ → ℂ := fun v => f (v + u) * conj (f v)
  let M : ℝ → ℝ := fun v =>
    (93 / 100 : ℝ) * (Iio p1).indicator F v +
      (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) +
      (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v +
      (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) +
      (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v +
      (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) +
      (119 / 250 : ℝ) * (Ico p3 p4).indicator F v +
      (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u) +
      (101 / 250 : ℝ) * (Ico p4 p5).indicator F v +
      (125 / 202 : ℝ) * (Ico p5 p6).indicator F (v + u) +
      (311 / 1000 : ℝ) * (Ico p5 p6).indicator F v +
      (250 / 311 : ℝ) * (Ici p6).indicator F (v + u)
  have hq' : Integrable q' := by simpa [q', f] using logCorrelation_integrable_v25 g u
  have hind : ∀ (S : Set ℝ) (w : ℝ), 0 ≤ S.indicator F w :=
    fun S w => Set.indicator_nonneg (fun x _ => hF0 x) w
  have hT0 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v) := (hFi.indicator measurableSet_Iio).const_mul _
  have hT1 : Integrable (fun v => (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u)) := ((hFi.indicator measurableSet_Ico).comp_add_right u).const_mul _
  have hT2 : Integrable (fun v => (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v) := (hFi.indicator measurableSet_Ico).const_mul _
  have hT3 : Integrable (fun v => (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u)) := ((hFi.indicator measurableSet_Ico).comp_add_right u).const_mul _
  have hT4 : Integrable (fun v => (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v) := (hFi.indicator measurableSet_Ico).const_mul _
  have hT5 : Integrable (fun v => (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u)) := ((hFi.indicator measurableSet_Ico).comp_add_right u).const_mul _
  have hT6 : Integrable (fun v => (119 / 250 : ℝ) * (Ico p3 p4).indicator F v) := (hFi.indicator measurableSet_Ico).const_mul _
  have hT7 : Integrable (fun v => (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u)) := ((hFi.indicator measurableSet_Ico).comp_add_right u).const_mul _
  have hT8 : Integrable (fun v => (101 / 250 : ℝ) * (Ico p4 p5).indicator F v) := (hFi.indicator measurableSet_Ico).const_mul _
  have hT9 : Integrable (fun v => (125 / 202 : ℝ) * (Ico p5 p6).indicator F (v + u)) := ((hFi.indicator measurableSet_Ico).comp_add_right u).const_mul _
  have hT10 : Integrable (fun v => (311 / 1000 : ℝ) * (Ico p5 p6).indicator F v) := (hFi.indicator measurableSet_Ico).const_mul _
  have hT11 : Integrable (fun v => (250 / 311 : ℝ) * (Ici p6).indicator F (v + u)) := ((hFi.indicator measurableSet_Ici).comp_add_right u).const_mul _
  have hS1 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u)) := hT0.add hT1
  have hS2 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v) := hS1.add hT2
  have hS3 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u)) := hS2.add hT3
  have hS4 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v) := hS3.add hT4
  have hS5 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u)) := hS4.add hT5
  have hS6 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v) := hS5.add hT6
  have hS7 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v + (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u)) := hS6.add hT7
  have hS8 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v + (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u) + (101 / 250 : ℝ) * (Ico p4 p5).indicator F v) := hS7.add hT8
  have hS9 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v + (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u) + (101 / 250 : ℝ) * (Ico p4 p5).indicator F v + (125 / 202 : ℝ) * (Ico p5 p6).indicator F (v + u)) := hS8.add hT9
  have hS10 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v + (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u) + (101 / 250 : ℝ) * (Ico p4 p5).indicator F v + (125 / 202 : ℝ) * (Ico p5 p6).indicator F (v + u) + (311 / 1000 : ℝ) * (Ico p5 p6).indicator F v) := hS9.add hT10
  have hS11 : Integrable (fun v => (93 / 100 : ℝ) * (Iio p1).indicator F v + (25 / 93 : ℝ) * (Ico p1 p2).indicator F (v + u) + (661 / 1000 : ℝ) * (Ico p1 p2).indicator F v + (250 / 661 : ℝ) * (Ico p2 p3).indicator F (v + u) + (551 / 1000 : ℝ) * (Ico p2 p3).indicator F v + (250 / 551 : ℝ) * (Ico p3 p4).indicator F (v + u) + (119 / 250 : ℝ) * (Ico p3 p4).indicator F v + (125 / 238 : ℝ) * (Ico p4 p5).indicator F (v + u) + (101 / 250 : ℝ) * (Ico p4 p5).indicator F v + (125 / 202 : ℝ) * (Ico p5 p6).indicator F (v + u) + (311 / 1000 : ℝ) * (Ico p5 p6).indicator F v + (250 / 311 : ℝ) * (Ici p6).indicator F (v + u)) := hS10.add hT11
  have hM : Integrable M := hS11
  have hpoint : ∀ v : ℝ, ‖q' v‖ ≤ M v := by
    intro v
    have hMnn : 0 ≤ M v := by
      unfold M
      have := hind (Iio p1) v
      have := hind (Ico p1 p2) (v + u)
      have := hind (Ico p1 p2) v
      have := hind (Ico p2 p3) (v + u)
      have := hind (Ico p2 p3) v
      have := hind (Ico p3 p4) (v + u)
      have := hind (Ico p3 p4) v
      have := hind (Ico p4 p5) (v + u)
      have := hind (Ico p4 p5) v
      have := hind (Ico p5 p6) (v + u)
      have := hind (Ico p5 p6) v
      have := hind (Ici p6) (v + u)
      positivity
    by_cases h0 : f v = 0
    · have : ‖q' v‖ = 0 := by simp [q', h0]
      rw [this]; exact hMnn
    by_cases h1 : f (v + u) = 0
    · have : ‖q' v‖ = 0 := by simp [q', h1]
      rw [this]; exact hMnn
    have hv := hw (subset_tsupport _ h0)
    have hvu := hw (subset_tsupport _ h1)
    have hv1 := hv.1
    have hvu2 := hvu.2
    have hnq : ‖q' v‖ = ‖f (v + u)‖ * ‖f v‖ := by simp [q']
    rw [hnq]
    set x := ‖f (v + u)‖ with hx
    set y := ‖f v‖ with hy
    by_cases hc1 : v < p1
    · -- v ∈ cell 0
      have hM' : M v = (93 / 100 : ℝ) * y ^ 2 + (25 / 93 : ℝ) * x ^ 2 := by
        unfold M
        rw [Set.indicator_of_mem (show v ∈ Iio p1 from by show v < p1; linarith),
          Set.indicator_of_mem (show v + u ∈ Ico p1 p2 from ⟨by linarith, by linarith⟩),
          Set.indicator_of_notMem (show v ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v + u ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v + u ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v + u ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v + u ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
          Set.indicator_of_notMem (show v + u ∉ Ici p6 from fun h => by change p6 ≤ v + u at h; linarith)]
        simp [F, hx, hy]
      rw [hM']
      nlinarith [sq_nonneg (y - (50 / 93 : ℝ) * x)]
    · have hc1' : p1 ≤ v := not_lt.mp hc1
      by_cases hc2 : v < p2
      · -- v ∈ cell 1
        have hM' : M v = (661 / 1000 : ℝ) * y ^ 2 + (250 / 661 : ℝ) * x ^ 2 := by
          unfold M
          rw [Set.indicator_of_notMem (show v ∉ Iio p1 from fun h => by change v < p1 at h; linarith),
            Set.indicator_of_notMem (show v + u ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_mem (show v ∈ Ico p1 p2 from ⟨by linarith, by linarith⟩),
            Set.indicator_of_mem (show v + u ∈ Ico p2 p3 from ⟨by linarith, by linarith⟩),
            Set.indicator_of_notMem (show v ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v + u ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v + u ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v + u ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
            Set.indicator_of_notMem (show v + u ∉ Ici p6 from fun h => by change p6 ≤ v + u at h; linarith)]
          simp [F, hx, hy]
        rw [hM']
        nlinarith [sq_nonneg (y - (500 / 661 : ℝ) * x)]
      · have hc2' : p2 ≤ v := not_lt.mp hc2
        by_cases hc3 : v < p3
        · -- v ∈ cell 2
          have hM' : M v = (551 / 1000 : ℝ) * y ^ 2 + (250 / 551 : ℝ) * x ^ 2 := by
            unfold M
            rw [Set.indicator_of_notMem (show v ∉ Iio p1 from fun h => by change v < p1 at h; linarith),
              Set.indicator_of_notMem (show v + u ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v + u ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_mem (show v ∈ Ico p2 p3 from ⟨by linarith, by linarith⟩),
              Set.indicator_of_mem (show v + u ∈ Ico p3 p4 from ⟨by linarith, by linarith⟩),
              Set.indicator_of_notMem (show v ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v + u ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v + u ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
              Set.indicator_of_notMem (show v + u ∉ Ici p6 from fun h => by change p6 ≤ v + u at h; linarith)]
            simp [F, hx, hy]
          rw [hM']
          nlinarith [sq_nonneg (y - (500 / 551 : ℝ) * x)]
        · have hc3' : p3 ≤ v := not_lt.mp hc3
          by_cases hc4 : v < p4
          · -- v ∈ cell 3
            have hM' : M v = (119 / 250 : ℝ) * y ^ 2 + (125 / 238 : ℝ) * x ^ 2 := by
              unfold M
              rw [Set.indicator_of_notMem (show v ∉ Iio p1 from fun h => by change v < p1 at h; linarith),
                Set.indicator_of_notMem (show v + u ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v + u ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v + u ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_mem (show v ∈ Ico p3 p4 from ⟨by linarith, by linarith⟩),
                Set.indicator_of_mem (show v + u ∈ Ico p4 p5 from ⟨by linarith, by linarith⟩),
                Set.indicator_of_notMem (show v ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v + u ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                Set.indicator_of_notMem (show v + u ∉ Ici p6 from fun h => by change p6 ≤ v + u at h; linarith)]
              simp [F, hx, hy]
            rw [hM']
            nlinarith [sq_nonneg (y - (125 / 119 : ℝ) * x)]
          · have hc4' : p4 ≤ v := not_lt.mp hc4
            by_cases hc5 : v < p5
            · -- v ∈ cell 4
              have hM' : M v = (101 / 250 : ℝ) * y ^ 2 + (125 / 202 : ℝ) * x ^ 2 := by
                unfold M
                rw [Set.indicator_of_notMem (show v ∉ Iio p1 from fun h => by change v < p1 at h; linarith),
                  Set.indicator_of_notMem (show v + u ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v + u ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v + u ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v + u ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_mem (show v ∈ Ico p4 p5 from ⟨by linarith, by linarith⟩),
                  Set.indicator_of_mem (show v + u ∈ Ico p5 p6 from ⟨by linarith, by linarith⟩),
                  Set.indicator_of_notMem (show v ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                  Set.indicator_of_notMem (show v + u ∉ Ici p6 from fun h => by change p6 ≤ v + u at h; linarith)]
                simp [F, hx, hy]
              rw [hM']
              nlinarith [sq_nonneg (y - (125 / 101 : ℝ) * x)]
            · have hc5' : p5 ≤ v := not_lt.mp hc5
              by_cases hc6 : v < p6
              · -- v ∈ cell 5
                have hM' : M v = (311 / 1000 : ℝ) * y ^ 2 + (250 / 311 : ℝ) * x ^ 2 := by
                  unfold M
                  rw [Set.indicator_of_notMem (show v ∉ Iio p1 from fun h => by change v < p1 at h; linarith),
                    Set.indicator_of_notMem (show v + u ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v + u ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v + u ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v + u ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_notMem (show v + u ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith),
                    Set.indicator_of_mem (show v ∈ Ico p5 p6 from ⟨by linarith, by linarith⟩),
                    Set.indicator_of_mem (show v + u ∈ Ici p6 from by show p6 ≤ v + u; linarith)]
                  simp [F, hx, hy]
                rw [hM']
                nlinarith [sq_nonneg (y - (500 / 311 : ℝ) * x)]
              · have hc6' : p6 ≤ v := not_lt.mp hc6
                exfalso
                linarith
  have hE : (∫ w : ℝ, F w) = energy g.1 := by
    simpa [F, f] using logLift_energy_eq_packet_energy g
  have hI0 : 0 ≤ ∫ w : ℝ, (Iio p1).indicator F w := integral_nonneg (fun w => hind (Iio p1) w)
  have hK0 : Integrable (fun w => (Iio p1).indicator F w) := hFi.indicator measurableSet_Iio
  have hsh0 : (∫ v : ℝ, (Iio p1).indicator F (v + u)) = ∫ w : ℝ, (Iio p1).indicator F w :=
    integral_add_right_eq_self (fun w => (Iio p1).indicator F w) u
  have hI1 : 0 ≤ ∫ w : ℝ, (Ico p1 p2).indicator F w := integral_nonneg (fun w => hind (Ico p1 p2) w)
  have hK1 : Integrable (fun w => (Ico p1 p2).indicator F w) := hFi.indicator measurableSet_Ico
  have hsh1 : (∫ v : ℝ, (Ico p1 p2).indicator F (v + u)) = ∫ w : ℝ, (Ico p1 p2).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p1 p2).indicator F w) u
  have hI2 : 0 ≤ ∫ w : ℝ, (Ico p2 p3).indicator F w := integral_nonneg (fun w => hind (Ico p2 p3) w)
  have hK2 : Integrable (fun w => (Ico p2 p3).indicator F w) := hFi.indicator measurableSet_Ico
  have hsh2 : (∫ v : ℝ, (Ico p2 p3).indicator F (v + u)) = ∫ w : ℝ, (Ico p2 p3).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p2 p3).indicator F w) u
  have hI3 : 0 ≤ ∫ w : ℝ, (Ico p3 p4).indicator F w := integral_nonneg (fun w => hind (Ico p3 p4) w)
  have hK3 : Integrable (fun w => (Ico p3 p4).indicator F w) := hFi.indicator measurableSet_Ico
  have hsh3 : (∫ v : ℝ, (Ico p3 p4).indicator F (v + u)) = ∫ w : ℝ, (Ico p3 p4).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p3 p4).indicator F w) u
  have hI4 : 0 ≤ ∫ w : ℝ, (Ico p4 p5).indicator F w := integral_nonneg (fun w => hind (Ico p4 p5) w)
  have hK4 : Integrable (fun w => (Ico p4 p5).indicator F w) := hFi.indicator measurableSet_Ico
  have hsh4 : (∫ v : ℝ, (Ico p4 p5).indicator F (v + u)) = ∫ w : ℝ, (Ico p4 p5).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p4 p5).indicator F w) u
  have hI5 : 0 ≤ ∫ w : ℝ, (Ico p5 p6).indicator F w := integral_nonneg (fun w => hind (Ico p5 p6) w)
  have hK5 : Integrable (fun w => (Ico p5 p6).indicator F w) := hFi.indicator measurableSet_Ico
  have hsh5 : (∫ v : ℝ, (Ico p5 p6).indicator F (v + u)) = ∫ w : ℝ, (Ico p5 p6).indicator F w :=
    integral_add_right_eq_self (fun w => (Ico p5 p6).indicator F w) u
  have hI6 : 0 ≤ ∫ w : ℝ, (Ici p6).indicator F w := integral_nonneg (fun w => hind (Ici p6) w)
  have hK6 : Integrable (fun w => (Ici p6).indicator F w) := hFi.indicator measurableSet_Ici
  have hsh6 : (∫ v : ℝ, (Ici p6).indicator F (v + u)) = ∫ w : ℝ, (Ici p6).indicator F w :=
    integral_add_right_eq_self (fun w => (Ici p6).indicator F w) u
  have hP1 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w) := hK0.add hK1
  have hP2 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w + (Ico p2 p3).indicator F w) := hP1.add hK2
  have hP3 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w + (Ico p2 p3).indicator F w + (Ico p3 p4).indicator F w) := hP2.add hK3
  have hP4 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w + (Ico p2 p3).indicator F w + (Ico p3 p4).indicator F w + (Ico p4 p5).indicator F w) := hP3.add hK4
  have hP5 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w + (Ico p2 p3).indicator F w + (Ico p3 p4).indicator F w + (Ico p4 p5).indicator F w + (Ico p5 p6).indicator F w) := hP4.add hK5
  have hP6 : Integrable (fun w => (Iio p1).indicator F w + (Ico p1 p2).indicator F w + (Ico p2 p3).indicator F w + (Ico p3 p4).indicator F w + (Ico p4 p5).indicator F w + (Ico p5 p6).indicator F w + (Ici p6).indicator F w) := hP5.add hK6
  have hsplit : (∫ w : ℝ, (Iio p1).indicator F w) + (∫ w : ℝ, (Ico p1 p2).indicator F w) + (∫ w : ℝ, (Ico p2 p3).indicator F w) + (∫ w : ℝ, (Ico p3 p4).indicator F w) + (∫ w : ℝ, (Ico p4 p5).indicator F w) + (∫ w : ℝ, (Ico p5 p6).indicator F w) + (∫ w : ℝ, (Ici p6).indicator F w) = ∫ w : ℝ, F w := by
    rw [← integral_add hK0 hK1, ← integral_add hP1 hK2, ← integral_add hP2 hK3, ← integral_add hP3 hK4, ← integral_add hP4 hK5, ← integral_add hP5 hK6]
    congr 1
    funext w
    by_cases hw1 : w < p1
    · simp [Set.indicator_of_mem (show w ∈ Iio p1 from by show w < p1; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
    · have hw1' : p1 ≤ w := not_lt.mp hw1
      by_cases hw2 : w < p2
      · simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_mem (show w ∈ Ico p1 p2 from ⟨by linarith, by linarith⟩), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
      · have hw2' : p2 ≤ w := not_lt.mp hw2
        by_cases hw3 : w < p3
        · simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_mem (show w ∈ Ico p2 p3 from ⟨by linarith, by linarith⟩), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
        · have hw3' : p3 ≤ w := not_lt.mp hw3
          by_cases hw4 : w < p4
          · simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_mem (show w ∈ Ico p3 p4 from ⟨by linarith, by linarith⟩), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
          · have hw4' : p4 ≤ w := not_lt.mp hw4
            by_cases hw5 : w < p5
            · simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_mem (show w ∈ Ico p4 p5 from ⟨by linarith, by linarith⟩), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
            · have hw5' : p5 ≤ w := not_lt.mp hw5
              by_cases hw6 : w < p6
              · simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_mem (show w ∈ Ico p5 p6 from ⟨by linarith, by linarith⟩), Set.indicator_of_notMem (show w ∉ Ici p6 from fun h => by change p6 ≤ w at h; linarith)]
              · have hw6' : p6 ≤ w := not_lt.mp hw6
                simp [Set.indicator_of_notMem (show w ∉ Iio p1 from fun h => by change w < p1 at h; linarith), Set.indicator_of_notMem (show w ∉ Ico p1 p2 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p2 p3 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p3 p4 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p4 p5 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_notMem (show w ∉ Ico p5 p6 from fun h => by obtain ⟨h1, h2⟩ := h; linarith), Set.indicator_of_mem (show w ∈ Ici p6 from by show p6 ≤ w; linarith)]
  calc
    ‖logCorrelationV25 g u‖ = ‖∫ v : ℝ, q' v‖ := by rfl
    _ ≤ ∫ v : ℝ, ‖q' v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hq'.norm hM hpoint
    _ = (93 / 100 : ℝ) * (∫ v : ℝ, (Iio p1).indicator F v) +
          (25 / 93 : ℝ) * (∫ v : ℝ, (Ico p1 p2).indicator F (v + u)) +
          (661 / 1000 : ℝ) * (∫ v : ℝ, (Ico p1 p2).indicator F v) +
          (250 / 661 : ℝ) * (∫ v : ℝ, (Ico p2 p3).indicator F (v + u)) +
          (551 / 1000 : ℝ) * (∫ v : ℝ, (Ico p2 p3).indicator F v) +
          (250 / 551 : ℝ) * (∫ v : ℝ, (Ico p3 p4).indicator F (v + u)) +
          (119 / 250 : ℝ) * (∫ v : ℝ, (Ico p3 p4).indicator F v) +
          (125 / 238 : ℝ) * (∫ v : ℝ, (Ico p4 p5).indicator F (v + u)) +
          (101 / 250 : ℝ) * (∫ v : ℝ, (Ico p4 p5).indicator F v) +
          (125 / 202 : ℝ) * (∫ v : ℝ, (Ico p5 p6).indicator F (v + u)) +
          (311 / 1000 : ℝ) * (∫ v : ℝ, (Ico p5 p6).indicator F v) +
          (250 / 311 : ℝ) * (∫ v : ℝ, (Ici p6).indicator F (v + u)) := by
      unfold M
      rw [integral_add hS10 hT11, integral_add hS9 hT10, integral_add hS8 hT9, integral_add hS7 hT8, integral_add hS6 hT7, integral_add hS5 hT6, integral_add hS4 hT5, integral_add hS3 hT4, integral_add hS2 hT3, integral_add hS1 hT2, integral_add hT0 hT1]
      simp only [integral_const_mul]
    _ ≤ (93 / 100 : ℝ) * energy g.1 := by
      rw [hsh1, hsh2, hsh3, hsh4, hsh5, hsh6, ← hE, ← hsplit]
      nlinarith [hI0, hI1, hI2, hI3, hI4, hI5, hI6]

end AEGIS.RHCellCapsV13

#print axioms AEGIS.RHCellCapsV13.cell7_logCorrelation
