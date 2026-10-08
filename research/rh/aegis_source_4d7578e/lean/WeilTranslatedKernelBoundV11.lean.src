import RHTranslatedKernelDominanceV1
import WeilThreeBlockTranslatedPacketsV22
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — universal translated-kernel dominance V11.

This module upgrades the previous zero-shift equivalence to every real
translation.

The key observation is exact and elementary: the unitary multiplicative
translation used by the repository leaves the multiplicative
autocorrelation unchanged.  Hence the two diagonal arithmetic terms are
identical.  FinalSignResidualV1 can then be applied to the two-point packets
g + c T_t g for the four phases c in {1,-1,i,-i}, and the existing four-phase
reconstruction yields the full component box for every t.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilTranslatedKernelBoundV11

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHTranslatedKernelDominanceV1
open AEGIS.WeilMixedAlgebraV2

/-- Simultaneous unitary multiplicative translation leaves the actual
autocorrelation function exactly unchanged. -/
theorem autocorrelation_translate_invariant_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    WeilAutocorrelationV1 (translatePacket g d) =
      WeilAutocorrelationV1 g := by
  funext x
  unfold WeilAutocorrelationV1
  let b : ℝ := Real.exp (-d)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hc :
      Real.exp (-d / 2) * Real.exp (-d / 2) = b := by
    dsimp [b]
    rw [← Real.exp_add]
    congr 1
    ring
  let F : ℝ → ℂ := fun y =>
    g.1 (x * y) * conj (g.1 y)
  have hchange :=
    integral_comp_mul_left_Ioi' F 0 hb
  simp only [mul_zero] at hchange
  change
    (∫ y in Ioi (0 : ℝ),
      ((Real.exp (-d / 2) : ℂ) *
        g.1 (Real.exp (-d) * (x * y))) *
      conj ((Real.exp (-d / 2) : ℂ) *
        g.1 (Real.exp (-d) * y))) =
      ∫ y in Ioi (0 : ℝ), F y
  have hpoint :
      (fun y : ℝ =>
        ((Real.exp (-d / 2) : ℂ) *
          g.1 (Real.exp (-d) * (x * y))) *
        conj ((Real.exp (-d / 2) : ℂ) *
          g.1 (Real.exp (-d) * y))) =
      (fun y : ℝ => (b : ℂ) * F (b * y)) := by
    funext y
    dsimp [F, b]
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    rw [← mul_assoc]
    have hcC :
        (Real.exp (-d / 2) : ℂ) *
          (Real.exp (-d / 2) : ℂ) =
          (Real.exp (-d) : ℂ) := by
      exact_mod_cast hc
    rw [hcC]
    congr 2
    · congr 1
      ring
    · rfl
  rw [hpoint]
  have hsmul :
      (∫ y in Ioi (0 : ℝ), (b : ℂ) * F (b * y)) =
        b • (∫ y in Ioi (0 : ℝ), F (b * y)) := by
    rw [← integral_const_mul]
    simp [Complex.real_smul]
  rw [hsmul]
  exact hchange

/-- Therefore the diagonal mixed arithmetic form is translation invariant. -/
theorem B_translate_diagonal_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    B (translatePacket g d) (translatePacket g d) = B g g := by
  unfold B
  rw [AEGIS.WeilMixedClosureV2.diagonal_eq,
    AEGIS.WeilMixedClosureV2.diagonal_eq,
    autocorrelation_translate_invariant_v11]

/-- Mellin transform respects the mixed-algebra scale packet. -/
theorem mellin_scalePacket_v11
    (z : ℂ) (g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (scalePacket z g).1 s = z * mellin g.1 s := by
  change mellin (fun x : ℝ => z * g.1 x) s = _
  simpa [smul_eq_mul] using mellin_const_smul g.1 s z

/-- Mellin transform respects the mixed-algebra add packet. -/
theorem mellin_addPacket_v11
    (g h : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (addPacket g h).1 s =
      mellin g.1 s + mellin h.1 s := by
  have hg := weil_compact_smooth_mellin_convergent_all_v1 g s
  have hh := weil_compact_smooth_mellin_convergent_all_v1 h s
  have ha := hasMellin_add hg hh
  change mellin (fun x : ℝ => g.1 x + h.1 x) s = _
  exact ha.2

/-- Mellin transform of the exact two-point packet. -/
theorem mellin_twoPointPacket_v11
    (g h : WeilCompactSmoothGV1) (c s : ℂ) :
    mellin (TwoPointPacketV1 g h c).1 s =
      mellin g.1 s + c * mellin h.1 s := by
  unfold TwoPointPacketV1 combo
  rw [mellin_addPacket_v11, mellin_addPacket_v11,
    mellin_scalePacket_v11, mellin_scalePacket_v11,
    mellin_scalePacket_v11]
  simp
  ring

/-- The two-point packet remains in the exact two-moment domain whenever
both inputs do. -/
theorem twoPointPacket_preserves_moments_v11
    (g h : WeilCompactSmoothGV1) (c : ℂ)
    (hg : WeilMomentConditionsV1 g)
    (hh : WeilMomentConditionsV1 h) :
    WeilMomentConditionsV1 (TwoPointPacketV1 g h c) := by
  have hg0 :
      mellin g.1 0 = 0 :=
    (weil_mellin_zero_eq_moment0_v1 g).trans hg.1
  have hh0 :
      mellin h.1 0 = 0 :=
    (weil_mellin_zero_eq_moment0_v1 h).trans hh.1
  have hg1 :
      mellin g.1 1 = 0 :=
    (weil_mellin_one_eq_moment1_v1 g).trans hg.2
  have hh1 :
      mellin h.1 1 = 0 :=
    (weil_mellin_one_eq_moment1_v1 h).trans hh.2
  constructor
  · rw [← weil_mellin_zero_eq_moment0_v1
      (TwoPointPacketV1 g h c),
      mellin_twoPointPacket_v11, hg0, hh0]
    simp
  · rw [← weil_mellin_one_eq_moment1_v1
      (TwoPointPacketV1 g h c),
      mellin_twoPointPacket_v11, hg1, hh1]
    simp

/-- Final sign forces the exact two-point component box for every translated
copy of every moment-zero test packet. -/
theorem final_sign_implies_translate_component_bounds_v11
    (hSign : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    ArithmeticComponentBoundsV1 g (translatePacket g d) := by
  let h := translatePacket g d
  have hhm : WeilMomentConditionsV1 h :=
    translate_preserves_moments g d hm
  have hdiag :
      (B h h).re = (B g g).re := by
    rw [B_translate_diagonal_v11 g d]

  have hphase :
      ∀ c : ℂ, WeilFourPhaseV1 c →
        0 ≤ WeilTwoPointValueV1
          (ArithmeticDiagonalV1 g)
          (ArithmeticCrossV1 g h)
          c := by
    intro c hc
    have hmom :
        WeilMomentConditionsV1 (TwoPointPacketV1 g h c) :=
      twoPointPacket_preserves_moments_v11 g h c hm hhm
    have hs :=
      hSign (TwoPointPacketV1 g h c) hmom
    have heq :=
      neg_actual_two_point_eq_weil_two_point_v1
        g h c hdiag
    rw [← heq]
    linarith

  exact
    (weil_four_phase_nonnegative_iff_components_v1
      (ArithmeticDiagonalV1 g)
      (ArithmeticCrossV1 g h)).1 hphase

/-- Uniform real/imaginary boundedness of the translated arithmetic cross
kernel. -/
theorem final_sign_implies_translate_cross_bounds_v11
    (hSign : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    |(ArithmeticCrossV1 g (translatePacket g d)).re| ≤
        ArithmeticDiagonalV1 g ∧
      |(ArithmeticCrossV1 g (translatePacket g d)).im| ≤
        ArithmeticDiagonalV1 g :=
  final_sign_implies_translate_component_bounds_v11 hSign g hm d

end AEGIS.WeilTranslatedKernelBoundV11

#print axioms AEGIS.WeilTranslatedKernelBoundV11.autocorrelation_translate_invariant_v11
#print axioms AEGIS.WeilTranslatedKernelBoundV11.B_translate_diagonal_v11
#print axioms AEGIS.WeilTranslatedKernelBoundV11.twoPointPacket_preserves_moments_v11
#print axioms AEGIS.WeilTranslatedKernelBoundV11.final_sign_implies_translate_component_bounds_v11
