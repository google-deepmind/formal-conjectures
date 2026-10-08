import WeilPairedZeroEvaluationV9
import WeilMixedAlgebraV2
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic

/-!
AEGIS Ω — exact Mellin-detecting seed packet V10.

For every target s : ℂ we construct a compact-smooth positive-half-line packet
whose Mellin transform at s is provably nonzero.

The construction is in logarithmic coordinates.  Let η be a fixed nonnegative
smooth bump around 0 with positive integral, and set

  h_s(u) = η(u) * exp(-s u).

After transporting h_s to x = exp(u), the Mellin kernel exp(su) cancels the
modulation exactly, leaving ∫η > 0.

This removes the approximate-identity limit from the off-line-zero witness
construction: detection at one prescribed spectral point is exact.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilOffLineSeedV10

open AEGIS.WeilPairedZeroEvaluationV9

/-- Fixed real bump in logarithmic coordinates. -/
def seedBumpV10 : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem seedBump_integral_pos_v10 :
    0 < ∫ u : ℝ, seedBumpV10 u := by
  exact seedBumpV10.integral_pos

/-- Complex modulation chosen to cancel the Mellin exponential at s. -/
def seedProfileV10 (s : ℂ) (u : ℝ) : ℂ :=
  ((seedBumpV10 u : ℝ) : ℂ) *
    Complex.exp (-s * (u : ℂ))

theorem seedProfile_contDiff_v10 (s : ℂ) :
    ContDiff ℝ ∞ (seedProfileV10 s) := by
  unfold seedProfileV10
  have hb :
      ContDiff ℝ ∞ (fun u : ℝ => ((seedBumpV10 u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp seedBumpV10.contDiff
  have he :
      ContDiff ℝ ∞
        (fun u : ℝ => Complex.exp (-s * (u : ℂ))) := by
    fun_prop
  exact hb.mul he

private theorem seedBump_zero_below_v10 {u : ℝ} (hu : u ≤ -1) :
    seedBumpV10 u = 0 := by
  apply seedBumpV10.zero_of_le_dist
  change (1 : ℝ) ≤ dist u 0
  rw [Real.dist_eq, sub_zero, abs_of_nonpos (by linarith)]
  linarith

private theorem seedBump_zero_above_v10 {u : ℝ} (hu : 1 ≤ u) :
    seedBumpV10 u = 0 := by
  apply seedBumpV10.zero_of_le_dist
  change (1 : ℝ) ≤ dist u 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
  exact hu

theorem seedProfile_zero_below_v10 (s : ℂ) {u : ℝ} (hu : u ≤ -1) :
    seedProfileV10 s u = 0 := by
  simp [seedProfileV10, seedBump_zero_below_v10 hu]

theorem seedProfile_zero_above_v10 (s : ℂ) {u : ℝ} (hu : 1 ≤ u) :
    seedProfileV10 s u = 0 := by
  simp [seedProfileV10, seedBump_zero_above_v10 hu]

/-- Positive-half-line guarded transport of the complex log profile. -/
def seedPacketFnV10 (s : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then seedProfileV10 s (Real.log x) else 0

theorem seedPacketFn_of_pos_v10 (s : ℂ) {x : ℝ} (hx : 0 < x) :
    seedPacketFnV10 s x = seedProfileV10 s (Real.log x) :=
  if_pos hx

theorem seedPacketFn_of_nonpos_v10 (s : ℂ) {x : ℝ} (hx : x ≤ 0) :
    seedPacketFnV10 s x = 0 :=
  if_neg (not_lt.2 hx)

theorem seedPacketFn_zero_below_v10 (s : ℂ) {x : ℝ}
    (hx : x ≤ Real.exp (-1)) :
    seedPacketFnV10 s x = 0 := by
  rcases le_or_gt x 0 with h | h
  · exact seedPacketFn_of_nonpos_v10 s h
  · rw [seedPacketFn_of_pos_v10 s h]
    apply seedProfile_zero_below_v10
    have hlog :=
      (Real.log_le_log_iff h (Real.exp_pos (-1))).2 hx
    simpa using hlog

theorem seedPacketFn_zero_above_v10 (s : ℂ) {x : ℝ}
    (hx : Real.exp 1 ≤ x) :
    seedPacketFnV10 s x = 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  rw [seedPacketFn_of_pos_v10 s hxpos]
  apply seedProfile_zero_above_v10
  have hlog :=
    (Real.log_le_log_iff (Real.exp_pos 1) hxpos).2 hx
  simpa using hlog

theorem seedPacketFn_tsupport_subset_v10 (s : ℂ) :
    tsupport (seedPacketFnV10 s) ⊆
      Icc (Real.exp (-1)) (Real.exp 1) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hnot
  apply hx
  rcases not_and_or.mp (fun h => hnot ⟨h.1, h.2⟩) with h | h
  · exact seedPacketFn_zero_below_v10 s (le_of_not_ge h)
  · exact seedPacketFn_zero_above_v10 s (le_of_not_ge h)

theorem seedPacketFn_hasCompactSupport_v10 (s : ℂ) :
    HasCompactSupport (seedPacketFnV10 s) :=
  (isCompact_Icc :
    IsCompact (Icc (Real.exp (-1)) (Real.exp 1))).of_isClosed_subset
      (isClosed_tsupport _) (seedPacketFn_tsupport_subset_v10 s)

theorem seedPacketFn_tsupport_positive_v10 (s : ℂ) :
    tsupport (seedPacketFnV10 s) ⊆ Ioi 0 := by
  intro x hx
  have hI := seedPacketFn_tsupport_subset_v10 s hx
  exact lt_of_lt_of_le (Real.exp_pos (-1)) hI.1

theorem seedPacketFn_contDiff_v10 (s : ℂ) :
    ContDiff ℝ ∞ (seedPacketFnV10 s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · have hEq :
      seedPacketFnV10 s =ᶠ[𝓝 x]
        fun y => seedProfileV10 s (Real.log y) :=
      eventuallyEq_of_mem (Ioi_mem_nhds hx)
        (fun y hy => seedPacketFn_of_pos_v10 s hy)
    exact ContDiffAt.congr_of_eventuallyEq
      ((seedProfile_contDiff_v10 s).contDiffAt.comp x
        (Real.contDiffAt_log.2 (ne_of_gt hx))) hEq
  · have hmem : Iio (Real.exp (-1)) ∈ 𝓝 x :=
      Iio_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-1)))
    have hEq :
      seedPacketFnV10 s =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      eventuallyEq_of_mem hmem
        (fun y hy =>
          seedPacketFn_zero_below_v10 s (le_of_lt hy))
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hEq

/-- Concrete compact-smooth packet detecting s. -/
def seedPacketV10 (s : ℂ) : WeilCompactSmoothGV1 :=
  ⟨seedPacketFnV10 s,
    seedPacketFn_contDiff_v10 s,
    seedPacketFn_hasCompactSupport_v10 s,
    seedPacketFn_tsupport_positive_v10 s⟩

@[simp] theorem seedPacket_exp_apply_v10 (s : ℂ) (u : ℝ) :
    (seedPacketV10 s).1 (Real.exp u) = seedProfileV10 s u := by
  simp [seedPacketV10, seedPacketFnV10, Real.exp_pos, Real.log_exp]

/-- At the target exponent the log-coordinate modulation cancels exactly. -/
theorem seedPacket_mellin_self_v10 (s : ℂ) :
    mellin (seedPacketV10 s).1 s =
      ((∫ u : ℝ, seedBumpV10 u : ℝ) : ℂ) := by
  rw [mellin_eq_log_integral_v9]
  calc
    (∫ u : ℝ,
      WeilLogMellinIntegrandV9 (seedPacketV10 s) s u)
      =
      ∫ u : ℝ, ((seedBumpV10 u : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by
          unfold WeilLogMellinIntegrandV9
          rw [seedPacket_exp_apply_v10]
          unfold seedProfileV10
          let A : ℂ := s * (u : ℂ)
          calc
            Complex.exp A *
                (((seedBumpV10 u : ℝ) : ℂ) * Complex.exp (-A))
              =
                ((seedBumpV10 u : ℝ) : ℂ) *
                  (Complex.exp A * Complex.exp (-A)) := by ring
            _ = ((seedBumpV10 u : ℝ) : ℂ) := by
                  rw [← Complex.exp_add]
                  simp)
    _ = ((∫ u : ℝ, seedBumpV10 u : ℝ) : ℂ) := by
          rw [integral_ofReal]

/-- The constructed packet sees its target spectral point nontrivially. -/
theorem seedPacket_mellin_ne_zero_v10 (s : ℂ) :
    mellin (seedPacketV10 s).1 s ≠ 0 := by
  rw [seedPacket_mellin_self_v10]
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt seedBump_integral_pos_v10)


/-- Mellin transform is additive on repository packets; convergence is
automatic for the compact-smooth class. -/
theorem mellin_addPacket_v10
    (a b : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (AEGIS.WeilMixedAlgebraV2.addPacket a b).1 s =
      mellin a.1 s + mellin b.1 s := by
  have ha := weil_compact_smooth_mellin_convergent_all_v1 a s
  have hb := weil_compact_smooth_mellin_convergent_all_v1 b s
  have h := hasMellin_add ha hb
  simpa [AEGIS.WeilMixedAlgebraV2.addPacket] using h.2

/-- For any two prescribed spectral points there is one compact-smooth packet
whose Mellin transform is nonzero at both.  No approximation or genericity
argument is needed: one of seed(s), seed(t), or their sum works. -/
theorem exists_packet_mellin_ne_zero_pair_v10
    (s t : ℂ) :
    ∃ g : WeilCompactSmoothGV1,
      mellin g.1 s ≠ 0 ∧ mellin g.1 t ≠ 0 := by
  let gs := seedPacketV10 s
  let gt := seedPacketV10 t
  have hss : mellin gs.1 s ≠ 0 := by
    simpa [gs] using seedPacket_mellin_ne_zero_v10 s
  have htt : mellin gt.1 t ≠ 0 := by
    simpa [gt] using seedPacket_mellin_ne_zero_v10 t
  by_cases hst : mellin gs.1 t ≠ 0
  · exact ⟨gs, hss, hst⟩
  · by_cases hts : mellin gt.1 s ≠ 0
    · exact ⟨gt, hts, htt⟩
    · let gsum := AEGIS.WeilMixedAlgebraV2.addPacket gs gt
      have hs :
          mellin gsum.1 s = mellin gs.1 s := by
        rw [mellin_addPacket_v10]
        simp [hts]
      have ht :
          mellin gsum.1 t = mellin gt.1 t := by
        rw [mellin_addPacket_v10]
        simp [hst]
      refine ⟨gsum, ?_, ?_⟩
      · rw [hs]
        exact hss
      · rw [ht]
        exact htt

end AEGIS.WeilOffLineSeedV10

#print axioms AEGIS.WeilOffLineSeedV10.seedPacketFn_contDiff_v10
#print axioms AEGIS.WeilOffLineSeedV10.seedPacket_mellin_self_v10
#print axioms AEGIS.WeilOffLineSeedV10.seedPacket_mellin_ne_zero_v10
