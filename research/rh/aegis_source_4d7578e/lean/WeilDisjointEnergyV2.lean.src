import WeilThreeBlockComplexV2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact L2-energy decomposition on three pointwise disjoint supports.
Integrability hypotheses are retained, not replaced by totalized integrals.
The logarithmic/multiplicative change of variables is not claimed here. -/
open MeasureTheory Complex
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilDisjointEnergyV2

def energy (f : ℝ → ℂ) : ℝ := ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume

def l2 (f : ℝ → ℂ) : ℝ := Real.sqrt (energy f)

theorem energy_nonnegative (f : ℝ → ℂ) : 0 ≤ energy f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem square_l2 (f : ℝ → ℂ) : l2 f ^ 2 = energy f :=
  Real.sq_sqrt (energy_nonnegative f)

theorem disjoint_pointwise (z0 z1 z2 a b c : ℂ)
    (hab : a = 0 ∨ b = 0) (hac : a = 0 ∨ c = 0) (hbc : b = 0 ∨ c = 0) :
    ‖z0*a + z1*b + z2*c‖ ^ 2 =
      ‖z0‖ ^ 2 * ‖a‖ ^ 2 + ‖z1‖ ^ 2 * ‖b‖ ^ 2 + ‖z2‖ ^ 2 * ‖c‖ ^ 2 := by
  rcases hab with rfl | rfl
  · rcases hbc with rfl | rfl <;> simp [norm_mul, mul_pow]
  · rcases hac with rfl | rfl <;> simp [norm_mul, mul_pow]

theorem disjoint_integral (z0 z1 z2 : ℂ) (f0 f1 f2 : ℝ → ℂ)
    (h0 : Integrable (fun t => ‖f0 t‖ ^ 2) volume)
    (h1 : Integrable (fun t => ‖f1 t‖ ^ 2) volume)
    (h2 : Integrable (fun t => ‖f2 t‖ ^ 2) volume)
    (h01 : ∀ t, f0 t = 0 ∨ f1 t = 0)
    (h02 : ∀ t, f0 t = 0 ∨ f2 t = 0)
    (h12 : ∀ t, f1 t = 0 ∨ f2 t = 0) :
    energy (fun t => z0*f0 t + z1*f1 t + z2*f2 t) =
      ‖z0‖ ^ 2 * energy f0 + ‖z1‖ ^ 2 * energy f1 + ‖z2‖ ^ 2 * energy f2 := by
  unfold energy
  simp_rw [disjoint_pointwise z0 z1 z2 _ _ _ (h01 _) (h02 _) (h12 _)]
  have h0' : Integrable (fun t => ‖z0‖ ^ 2 * ‖f0 t‖ ^ 2) volume :=
    h0.const_mul _
  have h1' : Integrable (fun t => ‖z1‖ ^ 2 * ‖f1 t‖ ^ 2) volume :=
    h1.const_mul _
  have h2' : Integrable (fun t => ‖z2‖ ^ 2 * ‖f2 t‖ ^ 2) volume :=
    h2.const_mul _
  have hab :
      (∫ t : ℝ, ‖z0‖ ^ 2 * ‖f0 t‖ ^ 2 + ‖z1‖ ^ 2 * ‖f1 t‖ ^ 2 ∂volume) =
        (∫ t : ℝ, ‖z0‖ ^ 2 * ‖f0 t‖ ^ 2 ∂volume) +
          ∫ t : ℝ, ‖z1‖ ^ 2 * ‖f1 t‖ ^ 2 ∂volume := by
    simpa only [Pi.add_apply] using integral_add h0' h1'
  have habc :
      (∫ t : ℝ, (‖z0‖ ^ 2 * ‖f0 t‖ ^ 2 + ‖z1‖ ^ 2 * ‖f1 t‖ ^ 2) +
          ‖z2‖ ^ 2 * ‖f2 t‖ ^ 2 ∂volume) =
        (∫ t : ℝ, ‖z0‖ ^ 2 * ‖f0 t‖ ^ 2 + ‖z1‖ ^ 2 * ‖f1 t‖ ^ 2 ∂volume) +
          ∫ t : ℝ, ‖z2‖ ^ 2 * ‖f2 t‖ ^ 2 ∂volume := by
    simpa only [Pi.add_apply] using integral_add (h0'.add h1') h2'
  rw [habc, hab]
  simp only [integral_const_mul]

theorem quotient_free_norm_identity (z0 z1 z2 : ℂ) (f0 f1 f2 : ℝ → ℂ)
    (h0 : Integrable (fun t => ‖f0 t‖ ^ 2) volume)
    (h1 : Integrable (fun t => ‖f1 t‖ ^ 2) volume)
    (h2 : Integrable (fun t => ‖f2 t‖ ^ 2) volume)
    (h01 : ∀ t, f0 t = 0 ∨ f1 t = 0)
    (h02 : ∀ t, f0 t = 0 ∨ f2 t = 0)
    (h12 : ∀ t, f1 t = 0 ∨ f2 t = 0) :
    AEGIS.WeilThreeBlockComplexV2.weightedEnergy z0 z1 z2 (l2 f0) (l2 f1) (l2 f2) =
      energy (fun t => z0*f0 t + z1*f1 t + z2*f2 t) := by
  rw [AEGIS.WeilThreeBlockComplexV2.energy_expansion, square_l2, square_l2, square_l2]
  exact (disjoint_integral z0 z1 z2 f0 f1 f2 h0 h1 h2 h01 h02 h12).symm

end AEGIS.WeilDisjointEnergyV2
