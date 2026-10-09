import WeilDigammaIntegralReductionV1
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
AEGIS Ω — real-axis completion of the Gauss digamma series dependency.

This module closes the missing real-positive-axis half of the decomposition

  ψ(z) + γ = ∑_{n≥0} (1/(n+1) - 1/(z+n))

without importing Gauss's integral formula as an axiom.  The proof uses only
pinned Mathlib facts already present at 0df444a3:

* convexity of `log ∘ Real.Gamma`;
* the Gamma recurrence;
* `harmonic n - log n → γ`;
* `log (n+a) - log n → 0`;
* the existing AEGIS absolute-summability bound for `seriesTerm`.

This file intentionally proves the identity first for `x > 0`, viewed inside
`ℂ`.  Analytic continuation to the full half-plane `0 < re z` is a separate
next module so that a failure there cannot erase this closed real-axis slice.

AUTHORITY_EFFECT = NONE.
RH is not asserted here.
-/

open Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDigammaSeriesRealV1

open AEGIS.WeilDigammaIntegralReductionV1

local notation "γ" => Real.eulerMascheroniConstant

/-- Real specialization of the complex AEGIS digamma-series summand. -/
def realSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - 1 / (x + n)

/-- The existing complex summand is exactly the coercion of the real one on the
positive real axis. -/
theorem seriesTerm_ofReal_v1 (x : ℝ) (n : ℕ) :
    seriesTerm (x : ℂ) n = (realSeriesTerm x n : ℂ) := by
  simp [seriesTerm, realSeriesTerm]

/-- Absolute summability of the AEGIS complex series term follows from the
already-proved kernel-integral majorant. -/
theorem summable_norm_seriesTerm_v1 (z : ℂ) (hz : 0 < z.re) :
    Summable (fun n : ℕ => ‖seriesTerm z n‖) := by
  refine Summable.of_nonneg_of_le
    (fun n => norm_nonneg (seriesTerm z n))
    (fun n => ?_)
    (summable_integral_norm_kernelTerm z hz)
  rw [← integral_kernelTerm z hz n]
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- Local copy of the standard real-restriction uniqueness argument used
privately in Mathlib's `GammaDeriv`: if a holomorphic function agrees with a
real function on the real axis, its complex derivative there is the coerced
real derivative. -/
private lemma complex_deriv_of_real_restriction
    {F : ℂ → ℂ} {g : ℝ → ℝ} {g' x : ℝ}
    (hF : DifferentiableAt ℂ F x)
    (hg : HasDerivAt g g' x)
    (hFg : ∀ y : ℝ, F y = g y) :
    HasDerivAt F (g' : ℂ) x := by
  refine HasDerivAt.congr_deriv hF.hasDerivAt ?_
  rw [← (funext hFg ▸ hF.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

/-- On the positive real axis, Mathlib's complex digamma is the coercion of
the derivative of `log Γ`. -/
theorem digamma_ofReal_eq_logGamma_deriv_v1 (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) =
      ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hGreal : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (by
      intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith)
  have hGne : Real.Gamma x ≠ 0 :=
    Real.Gamma_ne_zero (by
      intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith)
  have hGcomplex : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      linarith)
  have hGc :
      HasDerivAt Complex.Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) :=
    complex_deriv_of_real_restriction
      hGcomplex hGreal.hasDerivAt (fun y => Complex.Gamma_ofReal y)
  have hGammaCast : Complex.Gamma (x : ℂ) = (Real.Gamma x : ℂ) :=
    Complex.Gamma_ofReal x
  have hlogDeriv :
      deriv f x = deriv Real.Gamma x / Real.Gamma x := by
    simpa [f, Function.comp_def] using
      deriv.log hGreal hGne
  rw [Complex.digamma_def, logDeriv_apply, hGc.deriv, hGammaCast, hlogDeriv,
    Complex.ofReal_div]

/-- Iterated logarithmic-Gamma derivative recurrence. -/
private theorem logGamma_deriv_shift_v1 (x : ℝ) (hx : 0 < x) (n : ℕ) :
    deriv (Real.log ∘ Real.Gamma) (x + (n : ℝ)) =
      deriv (Real.log ∘ Real.Gamma) x +
        ∑ k ∈ Finset.range n, 1 / (x + (k : ℝ)) := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hrec (y : ℝ) (hy : 0 < y) :
      f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hdiff {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_))
    · intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith
    · intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith
  have hderRec (y : ℝ) (hy : 0 < y) :
      deriv f (y + 1) = deriv f y + 1 / y := by
    rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
      ← deriv_add (hdiff <| by positivity) (Real.differentiableAt_log hy.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hy] using hrec
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hyn : 0 < x + (n : ℝ) := by positivity
      rw [Nat.cast_succ]
      rw [show x + ((n : ℝ) + 1) = (x + (n : ℝ)) + 1 by ring]
      rw [hderRec (x + (n : ℝ)) hyn, ih, Finset.sum_range_succ]
      ring

/-- The shifted logarithmic-Gamma derivative has the expected logarithmic
asymptotic along the positive real ray. -/
private theorem logGamma_deriv_shift_sub_log_tendsto_zero_v1
    (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun n : ℕ =>
        deriv (Real.log ∘ Real.Gamma) (x + (n : ℝ)) - Real.log n)
      atTop (𝓝 0) := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have hrec (y : ℝ) (hy : 0 < y) :
      f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hdiff {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_))
    · intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith
    · intro m hm
      have hmnonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith
  have hLB (n : ℕ) (hn : 0 < n) :
      Real.log ((n : ℝ) + (x - 1)) ≤ deriv f (x + (n : ℝ)) := by
    let a : ℝ := x + (n : ℝ) - 1
    let b : ℝ := x + (n : ℝ)
    have hn1_nat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1_nat
    have ha : 0 < a := by
      dsimp [a]
      linarith
    have hb : 0 < b := by
      dsimp [b]
      positivity
    have hab : a < b := by
      dsimp [a, b]
      linarith
    have hs :=
      hc.slope_le_deriv (mem_Ioi.mpr ha) (mem_Ioi.mpr hb) hab (hdiff hb)
    have hslope : slope f a b = Real.log a := by
      rw [slope_def_field]
      have hab1 : b - a = 1 := by
        dsimp [a, b]
        ring
      rw [hab1, div_one]
      have hab2 : a + 1 = b := by
        dsimp [a, b]
        ring
      rw [← hab2, hrec a ha, add_sub_cancel_left]
    calc
      Real.log ((n : ℝ) + (x - 1)) = Real.log a := by
        congr 1
        dsimp [a]
        ring
      _ = slope f a b := hslope.symm
      _ ≤ deriv f b := hs
      _ = deriv f (x + (n : ℝ)) := by rfl
  have hUB (n : ℕ) :
      deriv f (x + (n : ℝ)) ≤ Real.log ((n : ℝ) + x) := by
    let a : ℝ := x + (n : ℝ)
    let b : ℝ := a + 1
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hb : 0 < b := by
      dsimp [b]
      positivity
    have hab : a < b := by
      dsimp [b]
      linarith
    have hs :=
      hc.deriv_le_slope (mem_Ioi.mpr ha) (mem_Ioi.mpr hb) hab (hdiff ha)
    have hslope : slope f a b = Real.log a := by
      rw [slope_def_field]
      have hab1 : b - a = 1 := by
        dsimp [b]
        ring
      rw [hab1, div_one]
      rw [show b = a + 1 by rfl, hrec a ha, add_sub_cancel_left]
    simpa [a, add_comm] using hs.trans_eq hslope
  have hlow :
      Tendsto
        (fun n : ℕ =>
          Real.log ((n : ℝ) + (x - 1)) - Real.log n)
        atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_log_comp_add_sub_log (x - 1)).comp
        tendsto_natCast_atTop_atTop
  have hupp :
      Tendsto
        (fun n : ℕ =>
          Real.log ((n : ℝ) + x) - Real.log n)
        atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_log_comp_add_sub_log x).comp
        tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact sub_le_sub_right (hLB n hn) _
  · filter_upwards with n
    exact sub_le_sub_right (hUB n) _

/-- Real positive-axis Gauss digamma series. -/
theorem real_digamma_series_v1 (x : ℝ) (hx : 0 < x) :
    HasSum (realSeriesTerm x)
      (γ + deriv (Real.log ∘ Real.Gamma) x) := by
  have hsumComplex :=
    summable_norm_seriesTerm_v1 (x : ℂ) (by simpa using hx)
  have hsumNorm :
      Summable (fun n : ℕ => ‖realSeriesTerm x n‖) := by
    simpa [seriesTerm_ofReal_v1, Complex.norm_real] using hsumComplex
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsumNorm]
  have hshift :=
    logGamma_deriv_shift_sub_log_tendsto_zero_v1 x hx
  have hmain :=
    (Real.tendsto_harmonic_sub_log.sub hshift).add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => deriv (Real.log ∘ Real.Gamma) x)
          atTop (𝓝 (deriv (Real.log ∘ Real.Gamma) x)))
  convert hmain using 1
  · funext n
    have hharm :
        (harmonic n : ℝ) =
          ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
      simp [harmonic, one_div]
    have hshiftEq :=
      logGamma_deriv_shift_v1 x hx n
    unfold realSeriesTerm
    rw [Finset.sum_sub_distrib, ← hharm]
    have hrecip :
        (∑ k ∈ Finset.range n, 1 / (x + (k : ℝ))) =
          deriv (Real.log ∘ Real.Gamma) (x + (n : ℝ)) -
            deriv (Real.log ∘ Real.Gamma) x := by
      linarith
    rw [hrecip]
    ring
  · ring

/-- The missing digamma-series half on the positive real axis, in exactly the
complex `seriesTerm` language used by the existing AEGIS reduction. -/
theorem digamma_series_ofReal_v1 (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) + (γ : ℂ) =
      ∑' n : ℕ, seriesTerm (x : ℂ) n := by
  have hs := real_digamma_series_v1 x hx
  have htsum := hs.tsum_eq
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) htsum
  rw [Complex.ofReal_tsum] at hcast
  calc
    Complex.digamma (x : ℂ) + (γ : ℂ) =
        ((deriv (Real.log ∘ Real.Gamma) x + γ : ℝ) : ℂ) := by
          rw [digamma_ofReal_eq_logGamma_deriv_v1 x hx, Complex.ofReal_add]
    _ = ((γ + deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
          congr 1
          ring
    _ = ∑' n : ℕ, (realSeriesTerm x n : ℂ) := hcast.symm
    _ = ∑' n : ℕ, seriesTerm (x : ℂ) n := by
          apply tsum_congr
          intro n
          exact (seriesTerm_ofReal_v1 x n).symm

end AEGIS.WeilDigammaSeriesRealV1

#print axioms AEGIS.WeilDigammaSeriesRealV1.summable_norm_seriesTerm_v1
#print axioms AEGIS.WeilDigammaSeriesRealV1.digamma_ofReal_eq_logGamma_deriv_v1
#print axioms AEGIS.WeilDigammaSeriesRealV1.logGamma_deriv_shift_v1
#print axioms AEGIS.WeilDigammaSeriesRealV1.logGamma_deriv_shift_sub_log_tendsto_zero_v1
#print axioms AEGIS.WeilDigammaSeriesRealV1.real_digamma_series_v1
#print axioms AEGIS.WeilDigammaSeriesRealV1.digamma_series_ofReal_v1
