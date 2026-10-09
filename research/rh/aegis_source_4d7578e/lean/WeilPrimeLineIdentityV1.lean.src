import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Dirichlet
import WeilMellinInversionV1

/-!
AEGIS Ω — prime-side Mellin inversion with explicit analytic hypotheses.

The exchange of a Dirichlet series and the height integral is justified by
absolute integrability on the product, derived from L-series summability at a
real point and vertical integrability of the Mellin transform. No contour shift,
zero sum, explicit formula, positivity, or RH implication is asserted here.
-/

open Complex MeasureTheory
open scoped Topology

set_option autoImplicit false

noncomputable section

/-- The norm of an L-series term is constant along a vertical line. -/
theorem lseries_term_vertical_norm_v1
    (a : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((c : ℂ) + t * I) n‖ =
      ‖LSeries.term a (c : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

private theorem lseries_term_vertical_continuous_v1
    (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC]
    exact continuous_const.div (by fun_prop) (fun _ => Complex.exp_ne_zero _)

/-- Each product term is integrable; its dominating coefficient is independent
of height. The function `F` need only be vertically integrable. -/
theorem lseries_vertical_product_integrable_v1
    (a : ℕ → ℂ) (F : ℂ → ℂ) (c : ℝ)
    (hF : VerticalIntegrable F c) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n *
      F ((c : ℂ) + t * I)) := by
  refine (hF.norm.const_mul ‖LSeries.term a (c : ℂ) n‖).mono' ?_ ?_
  · exact (lseries_term_vertical_continuous_v1 a c n).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simp only [norm_mul, lseries_term_vertical_norm_v1]
      exact le_rfl

/-- Absolute product-integral summability, the precise Fubini hypothesis. -/
theorem lseries_vertical_product_integral_norm_summable_v1
    (a : ℕ → ℂ) (F : ℂ → ℂ) (c : ℝ)
    (ha : LSeriesSummable a (c : ℂ)) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((c : ℂ) + t * I) n * F ((c : ℂ) + t * I)‖) := by
  simp_rw [norm_mul, lseries_term_vertical_norm_v1, integral_const_mul]
  exact ha.norm.mul_right _

/-- The prime-side interchange as a `HasSum`, retaining both summability and
the value of the integral. -/
theorem lseries_vertical_product_hasSum_integral_v1
    (a : ℕ → ℂ) (F : ℂ → ℂ) (c : ℝ)
    (ha : LSeriesSummable a (c : ℂ)) (hF : VerticalIntegrable F c) :
    HasSum (fun n : ℕ => ∫ t : ℝ,
      LSeries.term a ((c : ℂ) + t * I) n * F ((c : ℂ) + t * I))
      (∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * F ((c : ℂ) + t * I)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (lseries_vertical_product_integrable_v1 a F c hF)
    (lseries_vertical_product_integral_norm_summable_v1 a F c ha)
  have heq : (∫ t : ℝ, ∑' n : ℕ,
      LSeries.term a ((c : ℂ) + t * I) n * F ((c : ℂ) + t * I)) =
      (∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * F ((c : ℂ) + t * I)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      have ht : LSeriesSummable a ((c : ℂ) + t * I) :=
        LSeriesSummable.of_re_le_re (by simp) ha
      exact (ht.hasSum.mul_right (F ((c : ℂ) + t * I))).tsum_eq
  rw [heq] at h
  exact h

private theorem lseries_mellin_term_inversion_v1
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (f : ℝ → ℂ) (c : ℝ)
    (hf : MellinConvergent f (c : ℂ))
    (hF : VerticalIntegrable (mellin f) c)
    (hcont : ∀ n : ℕ, n ≠ 0 → ContinuousAt f (n : ℝ)) (n : ℕ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n *
          mellin f ((c : ℂ) + t * I)) = a n * f (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  have hinv := mellinInv_mellin_eq c f
    (show (0 : ℝ) < (n : ℝ) by exact_mod_cast Nat.pos_of_ne_zero hn)
    hf hF (hcont n hn)
  calc
    _ = a n * mellinInv c (mellin f) (n : ℝ) := by
      have hk : (fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n *
          mellin f ((c : ℂ) + t * I)) =
          (fun t : ℝ => a n * ((n : ℂ) ^ (-((c : ℂ) + t * I)) *
            mellin f ((c : ℂ) + t * I))) := by
        funext t
        rw [LSeries.term_def₀ ha0]
        ring
      rw [hk, integral_const_mul]
      simp only [mellinInv, Complex.ofReal_natCast, Complex.real_smul, smul_eq_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := by rw [hinv]

/-- Dirichlet-series/Mellin inversion with the absolute exchange established,
rather than supplied as an assumption. -/
theorem lseries_mellin_prime_line_identity_v1
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (f : ℝ → ℂ) (c : ℝ)
    (ha : LSeriesSummable a (c : ℂ))
    (hf : MellinConvergent f (c : ℂ))
    (hF : VerticalIntegrable (mellin f) c)
    (hcont : ∀ n : ℕ, n ≠ 0 → ContinuousAt f (n : ℝ)) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, LSeries a ((c : ℂ) + t * I) *
          mellin f ((c : ℂ) + t * I)) =
      ∑' n : ℕ, a n * f (n : ℝ) := by
  have h := (lseries_vertical_product_hasSum_integral_v1 a (mellin f) c ha hF).const_smul
    (1 / (2 * Real.pi) : ℝ)
  have heq : (fun n : ℕ => (1 / (2 * Real.pi) : ℝ) •
      (∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n *
        mellin f ((c : ℂ) + t * I))) = (fun n : ℕ => a n * f (n : ℝ)) := by
    funext n
    exact lseries_mellin_term_inversion_v1 a ha0 f c hf hF hcont n
  rw [heq] at h
  exact h.tsum_eq.symm

/-- Specialization to the negative logarithmic derivative of the actual Riemann
zeta function on `c > 1`; compact support is not required by this abstract form. -/
theorem vonMangoldt_mellin_prime_line_identity_v1
    (f : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hf : MellinConvergent f (c : ℂ))
    (hF : VerticalIntegrable (mellin f) c)
    (hcont : ∀ n : ℕ, n ≠ 0 → ContinuousAt f (n : ℝ)) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) *
          mellin f ((c : ℂ) + t * I)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f (n : ℝ) := by
  have h := lseries_mellin_prime_line_identity_v1
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp) f c
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)) hf hF hcont
  convert h using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (show 1 < (((c : ℂ) + t * I) : ℂ).re by simpa using hc)]

/-- The prime-line identity for the actual AEGIS test-function class. Its
Mellin convergence, vertical integrability and continuity are proved inputs. -/
theorem weil_compact_smooth_prime_line_identity_v1
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) *
          mellin f.1 ((c : ℂ) + t * I)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f.1 (n : ℝ) := by
  exact vonMangoldt_mellin_prime_line_identity_v1 f.1 c hc
    (weil_compact_smooth_mellin_convergent_all_v1 f c)
    (weil_compact_smooth_mellin_vertical_integrable_all_v1 f c)
    (fun _ _ => f.2.1.continuous.continuousAt)
