import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — upper horizontal localization of Riemann-zeta zeros v1.

This lane proves only the strict upper real-part bound `Re ρ < 1` for every
Riemann-zeta zero, using Mathlib's pinned nonvanishing theorem on `Re s ≥ 1`.
It does not prove the lower real-part bound, a full critical-strip theorem,
height/radial truncation equivalence, an explicit formula, or RH.

UPPER_ZERO_LOCALIZATION_ONLY
LOWER_ZERO_LOCALIZATION_OPEN
HEIGHT_TRUNCATION_EQUIVALENCE_OPEN
EXPLICIT_FORMULA_THEOREM_OPEN
RH_EQUIVALENCE_OPEN
-/

open Complex

/-- Every zero of the Riemann zeta function has real part strictly below 1.

This is an RH-independent consequence of Mathlib's theorem
`riemannZeta_ne_zero_of_one_le_re`. -/
theorem riemann_zeta_zero_re_lt_one_v1 (rho : riemannZetaZeros) :
    rho.1.re < 1 := by
  by_contra h
  have hge : 1 ≤ rho.1.re := le_of_not_gt h
  exact (riemannZeta_ne_zero_of_one_le_re hge)
    (mem_riemannZetaZeros.mp rho.2)

#check riemann_zeta_zero_re_lt_one_v1
#print axioms riemann_zeta_zero_re_lt_one_v1
