import WeilFixedLineXSpaceTailV7
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
AEGIS Ω — reciprocal paired Mellin test closure v8.

For an existing compact-smooth positive-support test f, define

  f#(x) = x⁻¹ f(x⁻¹),    q = f + f#.

This module proves:
- f# remains in the exact existing `WeilCompactSmoothGV1` carrier;
- M f#(s) = M f(1-s);
- q remains in the carrier;
- M q(s) = M f(s) + M f(1-s);
- on s=c+it this is exactly the existing V5 paired Mellin profile.

No paired-zero Cauchy-kernel evaluation, zero-sum assembly, gamma/digamma
normalization, explicit-formula completion, arithmetic sign, global Weil
positivity, or RH conclusion is asserted here.
-/

open Set Filter Topology Complex MeasureTheory
open scoped ContDiff BigOperators

set_option autoImplicit false

noncomputable section

def WeilReciprocalFnV8
    (f : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  ((x⁻¹ : ℝ) : ℂ) * f.1 x⁻¹

def WeilReciprocalSupportEnvelopeV8
    (f : WeilCompactSmoothGV1) : Set ℝ :=
  (fun x : ℝ => x⁻¹) '' tsupport f.1

theorem weil_reciprocal_support_envelope_compact_v8
    (f : WeilCompactSmoothGV1) :
    IsCompact (WeilReciprocalSupportEnvelopeV8 f) := by
  apply f.2.2.1.image_of_continuousOn
  exact continuousOn_inv₀.mono (fun x hx =>
    ne_of_gt (f.2.2.2 hx))

theorem weil_reciprocal_support_envelope_positive_v8
    (f : WeilCompactSmoothGV1) :
    WeilReciprocalSupportEnvelopeV8 f ⊆ Ioi 0 := by
  rintro x ⟨y, hy, rfl⟩
  change 0 < y⁻¹
  exact inv_pos.mpr (f.2.2.2 hy)

theorem weil_reciprocal_tsupport_subset_v8
    (f : WeilCompactSmoothGV1) :
    tsupport (WeilReciprocalFnV8 f) ⊆
      WeilReciprocalSupportEnvelopeV8 f := by
  apply closure_minimal ?_
    (weil_reciprocal_support_envelope_compact_v8 f).isClosed
  intro x hx
  have hfne : f.1 x⁻¹ ≠ 0 := by
    intro hz
    apply hx
    simp [WeilReciprocalFnV8, hz]
  refine ⟨x⁻¹, subset_tsupport _ hfne, ?_⟩
  exact inv_inv x

theorem weil_reciprocal_hasCompactSupport_v8
    (f : WeilCompactSmoothGV1) :
    HasCompactSupport (WeilReciprocalFnV8 f) :=
  (weil_reciprocal_support_envelope_compact_v8 f).of_isClosed_subset
    (isClosed_tsupport _) (weil_reciprocal_tsupport_subset_v8 f)

theorem weil_reciprocal_tsupport_positive_v8
    (f : WeilCompactSmoothGV1) :
    tsupport (WeilReciprocalFnV8 f) ⊆ Ioi 0 :=
  (weil_reciprocal_tsupport_subset_v8 f).trans
    (weil_reciprocal_support_envelope_positive_v8 f)

theorem weil_reciprocal_contDiff_v8
    (f : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (WeilReciprocalFnV8 f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hK := weil_reciprocal_support_envelope_compact_v8 f
    have h0K : (0 : ℝ) ∉ WeilReciprocalSupportEnvelopeV8 f := by
      rintro ⟨y, hy, hiy⟩
      have hy0 : y ≠ 0 := ne_of_gt (f.2.2.2 hy)
      exact (inv_ne_zero hy0) hiy
    have hnhd :
        (WeilReciprocalSupportEnvelopeV8 f)ᶜ ∈ 𝓝 (0 : ℝ) :=
      hK.isClosed.isOpen_compl.mem_nhds h0K
    have heq :
        WeilReciprocalFnV8 f =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [hnhd] with y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hts
      exact hy (weil_reciprocal_tsupport_subset_v8 f hts)
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hinv :
        ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹) x :=
      contDiffAt_inv ℝ hx
    have hcoef :
        ContDiffAt ℝ ∞ (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hinv
    have hcomp :
        ContDiffAt ℝ ∞ (fun y : ℝ => f.1 y⁻¹) x :=
      f.2.1.contDiffAt.comp x hinv
    exact hcoef.mul hcomp

def WeilReciprocalCompactSmoothV8
    (f : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨WeilReciprocalFnV8 f,
    weil_reciprocal_contDiff_v8 f,
    weil_reciprocal_hasCompactSupport_v8 f,
    weil_reciprocal_tsupport_positive_v8 f⟩

theorem weil_reciprocal_compact_smooth_coe_v8
    (f : WeilCompactSmoothGV1) :
    (WeilReciprocalCompactSmoothV8 f).1 = WeilReciprocalFnV8 f := rfl

theorem weil_reciprocal_mellin_v8
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilReciprocalFnV8 f) s =
      mellin f.1 (1 - s) := by
  have hshift :=
    mellin_cpow_smul
      (fun x : ℝ => f.1 x⁻¹) s (-1 : ℂ)
  calc
    mellin (WeilReciprocalFnV8 f) s =
        mellin
          (fun x : ℝ =>
            ((x : ℂ) ^ (-1 : ℂ)) * f.1 x⁻¹) s := by
      congr 1
      funext x
      simp [WeilReciprocalFnV8, Complex.cpow_neg_one]
    _ = mellin (fun x : ℝ => f.1 x⁻¹) (s + (-1 : ℂ)) := by
      simpa only [smul_eq_mul] using hshift
    _ = mellin f.1 (-(s + (-1 : ℂ))) := by
      rw [mellin_comp_inv]
    _ = mellin f.1 (1 - s) := by
      congr 1
      ring

def WeilPairedTestV8
    (f : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨fun x => f.1 x + WeilReciprocalFnV8 f x,
    f.2.1.add (weil_reciprocal_contDiff_v8 f),
    f.2.2.1.add (weil_reciprocal_hasCompactSupport_v8 f),
    (tsupport_add f.1 (WeilReciprocalFnV8 f)).trans
      (union_subset f.2.2.2 (weil_reciprocal_tsupport_positive_v8 f))⟩

@[simp] theorem weil_paired_test_apply_v8
    (f : WeilCompactSmoothGV1) (x : ℝ) :
    (WeilPairedTestV8 f).1 x =
      f.1 x + WeilReciprocalFnV8 f x := rfl

theorem weil_paired_test_mellin_v8
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilPairedTestV8 f).1 s =
      mellin f.1 s + mellin f.1 (1 - s) := by
  have hf :=
    weil_compact_smooth_mellin_convergent_all_v1 f s
  have hr :=
    weil_compact_smooth_mellin_convergent_all_v1
      (WeilReciprocalCompactSmoothV8 f) s
  have hadd :=
    hasMellin_add hf hr
  calc
    mellin (WeilPairedTestV8 f).1 s =
        mellin f.1 s + mellin (WeilReciprocalFnV8 f) s := by
      simpa [WeilPairedTestV8,
        weil_reciprocal_compact_smooth_coe_v8] using hadd.2
    _ = mellin f.1 s + mellin f.1 (1 - s) := by
      rw [weil_reciprocal_mellin_v8]

theorem weil_paired_test_fixed_line_profile_v8
    (f : WeilCompactSmoothGV1) (c t : ℝ) :
    mellin (WeilPairedTestV8 f).1
        ((c : ℂ) + (t : ℂ) * I) =
      WeilPairedMellinProfileV5 f c t := by
  rw [weil_paired_test_mellin_v8]
  rw [weil_paired_mellin_profile_eq_one_sub_v5]

end

#print axioms weil_reciprocal_support_envelope_compact_v8
#print axioms weil_reciprocal_tsupport_subset_v8
#print axioms weil_reciprocal_contDiff_v8
#print axioms weil_reciprocal_mellin_v8
#print axioms weil_paired_test_mellin_v8
#print axioms weil_paired_test_fixed_line_profile_v8
