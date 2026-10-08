import WeilLogCoordinateIsometryV21
import WeilThreeBlockAnalyticConstantsV21
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — retained three-block translated packets V2.2.

Exact parent:
  Aegis-Omega/AEGIS-OMEGA@f86af1f59c3095ee13877dae7f91b3c5a8b637f4

Toolchain:
  Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474

This module is deliberately narrow.  It reuses the already kernel-verified
V2/V2.1 carrier, norm bridge and analytic constants.  It adds only the special
translated-profile construction

  T_d g(x) = exp(-d/2) g(exp(-d)x)

used for the concrete shifts -log 2, 0, +log 2.  It proves carrier membership,
log-lift translation, support translation, repository moment preservation,
energy preservation, and pairwise disjointness for a common width-1/32 packet.

It does NOT prove any Archimedean B-bound, global Weil sign or RH.
-/

open Set Function MeasureTheory Complex
open scoped ContDiff ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilThreeBlockTranslatedPacketsV22

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockAnalyticConstantsV21

def LogSupportIn (g : WeilCompactSmoothGV1) (lo hi : ℝ) : Prop :=
  tsupport (logLift g.1) ⊆ Icc lo hi

def WidthOneThirtyTwoAt (g : WeilCompactSmoothGV1) (a : ℝ) : Prop :=
  LogSupportIn g (a - (1 / 64 : ℝ)) (a + (1 / 64 : ℝ))

def translateFn (g : WeilCompactSmoothGV1) (d x : ℝ) : ℂ :=
  (Real.exp (-d / 2) : ℂ) * g.1 (Real.exp (-d) * x)

def translateEnvelope (g : WeilCompactSmoothGV1) (d : ℝ) : Set ℝ :=
  (fun y : ℝ => Real.exp d * y) '' tsupport g.1

theorem translateEnvelope_compact (g : WeilCompactSmoothGV1) (d : ℝ) :
    IsCompact (translateEnvelope g d) :=
  g.2.2.1.image (continuous_const.mul continuous_id)

theorem translateEnvelope_positive (g : WeilCompactSmoothGV1) (d : ℝ) :
    translateEnvelope g d ⊆ Ioi 0 := by
  rintro x ⟨y, hy, rfl⟩
  exact mul_pos (Real.exp_pos d) (g.2.2.2 hy)

theorem translate_tsupport_subset (g : WeilCompactSmoothGV1) (d : ℝ) :
    tsupport (translateFn g d) ⊆ translateEnvelope g d := by
  apply closure_minimal ?_ (translateEnvelope_compact g d).isClosed
  intro x hx
  by_contra hnot
  apply hx
  unfold translateFn
  have hg : g.1 (Real.exp (-d) * x) = 0 := by
    by_contra hgne
    apply hnot
    refine ⟨Real.exp (-d) * x, subset_tsupport _ hgne, ?_⟩
    calc
      Real.exp d * (Real.exp (-d) * x)
          = (Real.exp d * Real.exp (-d)) * x := by ring
      _ = x := by
        rw [← Real.exp_add]
        simp
  simp [hg]

theorem translate_hasCompactSupport (g : WeilCompactSmoothGV1) (d : ℝ) :
    HasCompactSupport (translateFn g d) :=
  (translateEnvelope_compact g d).of_isClosed_subset
    (isClosed_tsupport _) (translate_tsupport_subset g d)

theorem translate_tsupport_positive (g : WeilCompactSmoothGV1) (d : ℝ) :
    tsupport (translateFn g d) ⊆ Ioi 0 :=
  (translate_tsupport_subset g d).trans (translateEnvelope_positive g d)

theorem translate_contDiff (g : WeilCompactSmoothGV1) (d : ℝ) :
    ContDiff ℝ ∞ (translateFn g d) := by
  unfold translateFn
  exact contDiff_const.mul (g.2.1.comp (contDiff_const.mul contDiff_id))

def translatePacket (g : WeilCompactSmoothGV1) (d : ℝ) : WeilCompactSmoothGV1 :=
  ⟨translateFn g d, translate_contDiff g d,
    translate_hasCompactSupport g d, translate_tsupport_positive g d⟩

@[simp] theorem translatePacket_apply
    (g : WeilCompactSmoothGV1) (d x : ℝ) :
    (translatePacket g d).1 x =
      (Real.exp (-d / 2) : ℂ) * g.1 (Real.exp (-d) * x) := rfl

theorem logLift_translate (g : WeilCompactSmoothGV1) (d t : ℝ) :
    logLift (translatePacket g d).1 t = logLift g.1 (t - d) := by
  unfold logLift translatePacket translateFn
  dsimp
  have harg : Real.exp (-d) * Real.exp t = Real.exp (t - d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [harg]
  have hscalar :
      (Real.exp (t / 2) : ℂ) * (Real.exp (-d / 2) : ℂ) =
        (Real.exp ((t - d) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hscalar]

theorem log_mem_of_ne_zero
    (g : WeilCompactSmoothGV1) {lo hi x : ℝ}
    (hI : LogSupportIn g lo hi) (hx : 0 < x) (hg : g.1 x ≠ 0) :
    Real.log x ∈ Icc lo hi := by
  have hLift : logLift g.1 (Real.log x) ≠ 0 := by
    unfold logLift
    rw [Real.exp_log hx]
    exact mul_ne_zero (by simp) hg
  exact hI (subset_tsupport _ hLift)

theorem packet_eq_zero_of_nonpos
    (g : WeilCompactSmoothGV1) {x : ℝ} (hx : x ≤ 0) : g.1 x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_lt_of_ge hx) (g.2.2.2 hmem)

theorem translate_logSupportIn
    (g : WeilCompactSmoothGV1) (d lo hi : ℝ)
    (hI : LogSupportIn g lo hi) :
    LogSupportIn (translatePacket g d) (lo + d) (hi + d) := by
  unfold LogSupportIn
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  have hne : logLift (translatePacket g d).1 t ≠ 0 := ht
  rw [logLift_translate] at hne
  have hm : t - d ∈ tsupport (logLift g.1) := subset_tsupport _ hne
  have h := hI hm
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem pointwise_disjoint_of_log_intervals
    (p q : WeilCompactSmoothGV1)
    {plo phi qlo qhi : ℝ}
    (hp : LogSupportIn p plo phi)
    (hq : LogSupportIn q qlo qhi)
    (hsep : phi < qlo) :
    ∀ x : ℝ, p.1 x = 0 ∨ q.1 x = 0 := by
  intro x
  by_cases hx : 0 < x
  · by_cases hlog : Real.log x ≤ phi
    · right
      by_contra hq0
      have hm := log_mem_of_ne_zero q hq hx hq0
      linarith [hm.1]
    · left
      by_contra hp0
      have hm := log_mem_of_ne_zero p hp hx hp0
      linarith [hm.2]
  · left
    exact packet_eq_zero_of_nonpos p (le_of_not_gt hx)

theorem integral_exp_substitution_complex (f : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), f x) =
      ∫ t : ℝ, (Real.exp t) • f (Real.exp t) := by
  have h :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ))
      (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn f
  simpa [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _)] using h

def logMomentMinus (g : WeilCompactSmoothGV1) : ℂ :=
  ∫ t : ℝ, (Real.exp (-t / 2) : ℂ) * logLift g.1 t

def logMomentPlus (g : WeilCompactSmoothGV1) : ℂ :=
  ∫ t : ℝ, (Real.exp (t / 2) : ℂ) * logLift g.1 t

theorem logMomentMinus_eq_repository (g : WeilCompactSmoothGV1) :
    logMomentMinus g = ∫ x in Ioi (0 : ℝ), g.1 x / (x : ℂ) := by
  unfold logMomentMinus
  rw [integral_exp_substitution_complex]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold logLift
  rw [Complex.real_smul]
  have he : (Real.exp t : ℂ) ≠ 0 := by simp
  field_simp
  have hreal : Real.exp (-(t / 2)) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add]
    have hz : -(t / 2) + t / 2 = 0 := by ring
    rw [hz, Real.exp_zero]
  have hcomplex :
      (Real.exp (-(t / 2)) : ℂ) * (Real.exp (t / 2) : ℂ) = 1 := by
    exact_mod_cast hreal
  change ((Real.exp (-(t / 2)) : ℂ) * (Real.exp (t / 2) : ℂ)) *
      g.1 (Real.exp t) = g.1 (Real.exp t)
  rw [hcomplex, one_mul]

theorem logMomentPlus_eq_repository (g : WeilCompactSmoothGV1) :
    logMomentPlus g = ∫ x in Ioi (0 : ℝ), g.1 x := by
  unfold logMomentPlus
  rw [integral_exp_substitution_complex]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold logLift
  rw [Complex.real_smul]
  have h :
      (Real.exp (t / 2) : ℂ) * (Real.exp (t / 2) : ℂ) =
        (Real.exp t : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, h]

theorem translate_preserves_moments
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (translatePacket g d) := by
  have hmMinus : logMomentMinus g = 0 := by
    rw [logMomentMinus_eq_repository]
    exact hm.1
  have hmPlus : logMomentPlus g = 0 := by
    rw [logMomentPlus_eq_repository]
    exact hm.2
  have hMinus : logMomentMinus (translatePacket g d) =
      (Real.exp (-d / 2) : ℂ) * logMomentMinus g := by
    unfold logMomentMinus
    simp_rw [logLift_translate]
    calc
      (∫ t : ℝ, (Real.exp (-t / 2) : ℂ) * logLift g.1 (t - d))
          = ∫ t : ℝ, (Real.exp (-d / 2) : ℂ) *
              ((Real.exp (-(t - d) / 2) : ℂ) * logLift g.1 (t - d)) := by
              apply integral_congr_ae
              filter_upwards [] with t
              have hs : Real.exp (-t / 2) =
                  Real.exp (-d / 2) * Real.exp (-(t - d) / 2) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [show (Real.exp (-t / 2) : ℂ) =
                  (Real.exp (-d / 2) : ℂ) *
                    (Real.exp (-(t - d) / 2) : ℂ) by exact_mod_cast hs]
              ring
      _ = (Real.exp (-d / 2) : ℂ) *
            ∫ t : ℝ, (Real.exp (-(t - d) / 2) : ℂ) * logLift g.1 (t - d) := by
              rw [integral_const_mul]
      _ = (Real.exp (-d / 2) : ℂ) * logMomentMinus g := by
              unfold logMomentMinus
              congr 1
              simpa [sub_eq_add_neg] using
                (integral_add_right_eq_self
                  (fun s : ℝ => (Real.exp (-s / 2) : ℂ) * logLift g.1 s) (-d))
  have hPlus : logMomentPlus (translatePacket g d) =
      (Real.exp (d / 2) : ℂ) * logMomentPlus g := by
    unfold logMomentPlus
    simp_rw [logLift_translate]
    calc
      (∫ t : ℝ, (Real.exp (t / 2) : ℂ) * logLift g.1 (t - d))
          = ∫ t : ℝ, (Real.exp (d / 2) : ℂ) *
              ((Real.exp ((t - d) / 2) : ℂ) * logLift g.1 (t - d)) := by
              apply integral_congr_ae
              filter_upwards [] with t
              have hs : Real.exp (t / 2) =
                  Real.exp (d / 2) * Real.exp ((t - d) / 2) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [show (Real.exp (t / 2) : ℂ) =
                  (Real.exp (d / 2) : ℂ) *
                    (Real.exp ((t - d) / 2) : ℂ) by exact_mod_cast hs]
              ring
      _ = (Real.exp (d / 2) : ℂ) *
            ∫ t : ℝ, (Real.exp ((t - d) / 2) : ℂ) * logLift g.1 (t - d) := by
              rw [integral_const_mul]
      _ = (Real.exp (d / 2) : ℂ) * logMomentPlus g := by
              unfold logMomentPlus
              congr 1
              simpa [sub_eq_add_neg] using
                (integral_add_right_eq_self
                  (fun s : ℝ => (Real.exp (s / 2) : ℂ) * logLift g.1 s) (-d))
  constructor
  · rw [← logMomentMinus_eq_repository, hMinus, hmMinus, mul_zero]
  · rw [← logMomentPlus_eq_repository, hPlus, hmPlus, mul_zero]

theorem translate_energy (g : WeilCompactSmoothGV1) (d : ℝ) :
    energy (translatePacket g d).1 = energy g.1 := by
  rw [← logLift_energy_eq_packet_energy (translatePacket g d)]
  rw [← logLift_energy_eq_packet_energy g]
  simp_rw [logLift_translate]
  simpa [sub_eq_add_neg] using
    (integral_add_right_eq_self
      (fun s : ℝ => ‖logLift g.1 s‖ ^ 2) (-d))

def gMinus (g : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  translatePacket g (-Real.log 2)

def gZero (g : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  translatePacket g 0

def gPlus (g : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  translatePacket g (Real.log 2)

theorem log_two_gt_one_thirty_two : (1 / 32 : ℝ) < Real.log 2 := by
  exact (show (1 / 32 : ℝ) < 693 / 1000 by norm_num).trans log_two_lower

theorem three_blocks_preserve_moments
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (gMinus g) ∧
    WeilMomentConditionsV1 (gZero g) ∧
    WeilMomentConditionsV1 (gPlus g) := by
  exact ⟨translate_preserves_moments g (-Real.log 2) hm,
    translate_preserves_moments g 0 hm,
    translate_preserves_moments g (Real.log 2) hm⟩

theorem three_blocks_energy
    (g : WeilCompactSmoothGV1) :
    energy (gMinus g).1 = energy g.1 ∧
    energy (gZero g).1 = energy g.1 ∧
    energy (gPlus g).1 = energy g.1 := by
  exact ⟨translate_energy g (-Real.log 2), translate_energy g 0,
    translate_energy g (Real.log 2)⟩

theorem three_blocks_pairwise_disjoint
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (∀ x : ℝ, (gMinus g).1 x = 0 ∨ (gZero g).1 x = 0) ∧
    (∀ x : ℝ, (gMinus g).1 x = 0 ∨ (gPlus g).1 x = 0) ∧
    (∀ x : ℝ, (gZero g).1 x = 0 ∨ (gPlus g).1 x = 0) := by
  have hminus := translate_logSupportIn g (-Real.log 2)
    (a - (1 / 64 : ℝ)) (a + (1 / 64 : ℝ)) hw
  have hzero := translate_logSupportIn g 0
    (a - (1 / 64 : ℝ)) (a + (1 / 64 : ℝ)) hw
  have hplus := translate_logSupportIn g (Real.log 2)
    (a - (1 / 64 : ℝ)) (a + (1 / 64 : ℝ)) hw
  have hgap := log_two_gt_one_thirty_two
  constructor
  · apply pointwise_disjoint_of_log_intervals (gMinus g) (gZero g) hminus hzero
    linarith [hgap]
  constructor
  · apply pointwise_disjoint_of_log_intervals (gMinus g) (gPlus g) hminus hplus
    linarith [hgap]
  · apply pointwise_disjoint_of_log_intervals (gZero g) (gPlus g) hzero hplus
    linarith [hgap]

#print axioms logLift_translate
#print axioms translate_preserves_moments
#print axioms translate_energy
#print axioms three_blocks_pairwise_disjoint

end AEGIS.WeilThreeBlockTranslatedPacketsV22