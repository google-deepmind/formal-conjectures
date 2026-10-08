import WeilDigammaSeriesHalfPlaneV1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
AEGIS Ω — Gauss' digamma integral on the critical line (Epstein t-form kernel).

Specializes the repository's `gauss_digamma_integral_v1` to the real part on
`Re s = 1/2`, the form used by the PR #693 t-space target:

  Re ψ(1/2 + i t) − ψ(1/2) = ∫₀^∞ (1 − cos (t u)) / (2 sinh (u/2)) du.

Nothing here proves RH or any positivity statement.
-/

open Set Filter MeasureTheory Complex
open scoped Topology

noncomputable section

namespace AEGIS.EpsteinGaussCriticalLineV1

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1

/-- Real part of the difference of kernel terms at `1/2 + i t` and `1/2`. -/
def diffTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (kernelTerm (1 / 2 + t * I) n u - kernelTerm (1 / 2) n u).re

theorem diffTerm_eq (t : ℝ) (n : ℕ) (u : ℝ) :
    diffTerm t n u = Real.exp (-((n : ℝ) + 1 / 2) * u) * (1 - Real.cos (t * u)) := by
  simp only [diffTerm, kernelTerm, Complex.sub_re, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  have hc : Real.cos (-(t * u)) = Real.cos (t * u) := Real.cos_neg _
  ring_nf

theorem hasSum_seriesTerm (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun n => seriesTerm z n) (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (F := fun (n : ℕ) (u : ℝ) => kernelTerm z n u)
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun n => integrableOn_kernelTerm z hz n)
    (summable_integral_norm_kernelTerm z hz)
  have hs : Summable fun n => seriesTerm z n := by
    refine h.summable.congr fun n => ?_
    exact integral_kernelTerm z hz n
  rw [digamma_series_halfPlane_v1 z hz]
  exact hs.hasSum

theorem gauss_critical_line_v1 (t : ℝ) :
    (Complex.digamma (1 / 2 + t * I)).re - (Complex.digamma (1 / 2)).re
      = ∫ u in Ioi (0 : ℝ), (1 - Real.cos (t * u)) / (2 * Real.sinh (u / 2)) := by
  set z : ℂ := 1 / 2 + t * I with hzdef
  set w : ℂ := 1 / 2 with hwdef
  have hz : 0 < z.re := by rw [hzdef, hwdef]; simp
  have hw : 0 < w.re := by rw [hwdef]; norm_num
  -- integrability and summability of the real difference terms
  have hint : ∀ n, Integrable (diffTerm t n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    exact ((integrableOn_kernelTerm z hz n).sub (integrableOn_kernelTerm w hw n)).re
  have hnorm : ∀ n, (∫ u in Ioi (0 : ℝ), ‖diffTerm t n u‖)
      ≤ (∫ u in Ioi (0 : ℝ), ‖kernelTerm z n u‖) + ∫ u in Ioi (0 : ℝ), ‖kernelTerm w n u‖ := by
    intro n
    rw [← integral_add (integrableOn_kernelTerm z hz n).norm
      (integrableOn_kernelTerm w hw n).norm]
    refine integral_mono (hint n).norm
      ((integrableOn_kernelTerm z hz n).norm.add (integrableOn_kernelTerm w hw n).norm) ?_
    intro u
    simp only [diffTerm, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_sub_le _ _)
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖diffTerm t n u‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) hnorm
      ((summable_integral_norm_kernelTerm z hz).add (summable_integral_norm_kernelTerm w hw))
  have hHas := hasSum_integral_of_summable_integral_norm hint hsum
  -- each integral is the real part of a series-term difference
  have hterm : ∀ n, (∫ u in Ioi (0 : ℝ), diffTerm t n u) = (seriesTerm z n - seriesTerm w n).re := by
    intro n
    have hi : Integrable (fun u => kernelTerm z n u - kernelTerm w n u)
        (volume.restrict (Ioi (0 : ℝ))) :=
      (integrableOn_kernelTerm z hz n).sub (integrableOn_kernelTerm w hw n)
    calc (∫ u in Ioi (0 : ℝ), diffTerm t n u)
        = ∫ u in Ioi (0 : ℝ), RCLike.re (kernelTerm z n u - kernelTerm w n u) := rfl
      _ = RCLike.re (∫ u in Ioi (0 : ℝ), (kernelTerm z n u - kernelTerm w n u)) :=
          integral_re hi
      _ = (seriesTerm z n - seriesTerm w n).re := by
          rw [integral_sub (integrableOn_kernelTerm z hz n) (integrableOn_kernelTerm w hw n),
            integral_kernelTerm z hz n, integral_kernelTerm w hw n]
          rfl
  have hSeries : HasSum (fun n => (seriesTerm z n - seriesTerm w n).re)
      ((Complex.digamma z).re - (Complex.digamma w).re) := by
    have h := ((hasSum_seriesTerm z hz).sub (hasSum_seriesTerm w hw)).mapL Complex.reCLM
    simpa using h
  have hval : (∫ u in Ioi (0 : ℝ), ∑' n, diffTerm t n u)
      = (Complex.digamma z).re - (Complex.digamma w).re := by
    have h2 : HasSum (fun n => ∫ u in Ioi (0 : ℝ), diffTerm t n u)
        ((Complex.digamma z).re - (Complex.digamma w).re) := by
      simp only [hterm]; exact hSeries
    exact hHas.unique h2
  rw [← hval]
  -- pointwise geometric sum
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu : 0 < u := hu
  have hr0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hform : ∀ n : ℕ, diffTerm t n u
      = (Real.exp (-u / 2) * (1 - Real.cos (t * u))) * Real.exp (-u) ^ n := by
    intro n
    rw [diffTerm_eq, ← Real.exp_nat_mul, show -((n : ℝ) + 1 / 2) * u = -u / 2 + n * -u by ring,
      Real.exp_add]
    ring
  simp only [hform]
  rw [(hgeom.mul_left _).tsum_eq]
  have he : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have he2 : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hsinh : Real.sinh (u / 2) = (Real.exp (u / 2) - Real.exp (-u / 2)) / 2 := by
    rw [Real.sinh_eq]; ring_nf
  have hne : 1 - Real.exp (-u) ≠ 0 := by linarith
  have hne2 : Real.exp (u / 2) - Real.exp (-u / 2) ≠ 0 := by
    have : Real.exp (-u / 2) < Real.exp (u / 2) := Real.exp_lt_exp.2 (by linarith)
    linarith
  rw [hsinh, he2]
  rw [he2] at hne
  generalize Real.exp (-u / 2) = a at *
  generalize Real.exp (u / 2) = b at *
  generalize Real.cos (t * u) = c
  have hne' : 1 - a ^ 2 ≠ 0 := by rw [sq]; exact hne
  field_simp
  linear_combination (1 - c) * he

end AEGIS.EpsteinGaussCriticalLineV1

#print axioms AEGIS.EpsteinGaussCriticalLineV1.gauss_critical_line_v1
