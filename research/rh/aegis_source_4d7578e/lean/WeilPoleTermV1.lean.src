/-
AEGIS Ω — pole and prime-generating-function binding for the fixed-line Weil lane.

This is the theorem-bearing pole surface from PR #510, ported onto the #507
Lean 4.33.1 / Mathlib 0df444a3 pin.  The moving-contour obligation from #510
is deliberately NOT imported: the adopted #490 paired-Hadamard proof works on
a fixed line c > 1 and explicitly does not use horizontal contour segments.

This module proves only the pole residue and the von-Mangoldt L-series binding.
It does not prove the whole explicit formula, an arithmetic sign, global Weil
positivity, or RH.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet

open Filter Topology Complex

namespace WeilPoleTerm

noncomputable def zeta1LogDeriv (s : ℂ) : ℂ := deriv riemannZeta₁ s / riemannZeta₁ s

theorem zeta1LogDeriv_tendsto : Tendsto zeta1LogDeriv (𝓝 1) (𝓝 (deriv riemannZeta₁ 1)) := by
  have : ContinuousAt zeta1LogDeriv 1 := by
    apply ContinuousAt.div
    · exact (differentiable_riemannZeta₁.deriv).continuous.continuousAt
    · exact differentiable_riemannZeta₁.continuous.continuousAt
    · simp [riemannZeta₁_one]
  simpa [zeta1LogDeriv, riemannZeta₁_one] using this.tendsto

/-- `-ζ'/ζ` has a simple pole at `s = 1` with residue `1`. -/
theorem neg_logDeriv_riemannZeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s)))
      (𝓝[≠] 1) (𝓝 1) := by
  have key : (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s)))
      =ᶠ[𝓝[≠] 1] (fun s : ℂ => 1 - (s - 1) * zeta1LogDeriv s) := by
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, self_mem_nhdsWithin] with s hs hne
    have h1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hne
    rw [hs, zeta1LogDeriv]
    field_simp
    ring
  rw [tendsto_congr' key]
  have h0 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 ((1 : ℂ) - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h1 := zeta1LogDeriv_tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  simpa using tendsto_const_nhds.sub (h0.mul h1)

/-- For any transform continuous at `1`, the pole residue of `(-ζ'/ζ) F`
is exactly `F 1`. -/
theorem weil_pole_term_v1 (F : ℂ → ℂ) (hF : ContinuousAt F 1) :
    Tendsto (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s)) * F s)
      (𝓝[≠] 1) (𝓝 (F 1)) := by
  simpa using
    neg_logDeriv_riemannZeta_residue_one.mul (hF.tendsto.mono_left nhdsWithin_le_nhds)

theorem weil_pole_term_ne_zero_v1 (F : ℂ → ℂ) (hF : ContinuousAt F 1) (h1 : F 1 ≠ 0) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun s : ℂ => (s - 1) * (-(deriv riemannZeta s / riemannZeta s)) * F s)
        (𝓝[≠] 1) (𝓝 L) :=
  ⟨F 1, h1, weil_pole_term_v1 F hF⟩

/-- On `Re s > 1`, the von-Mangoldt L-series is the same `-ζ'/ζ` whose pole
was identified above. -/
theorem vonMangoldt_lseries_eq_neg_logDeriv_v1 {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = -(deriv riemannZeta s / riemannZeta s) := by
  simpa [neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

end WeilPoleTerm

#print axioms WeilPoleTerm.zeta1LogDeriv_tendsto
#print axioms WeilPoleTerm.neg_logDeriv_riemannZeta_residue_one
#print axioms WeilPoleTerm.weil_pole_term_v1
#print axioms WeilPoleTerm.weil_pole_term_ne_zero_v1
#print axioms WeilPoleTerm.vonMangoldt_lseries_eq_neg_logDeriv_v1
