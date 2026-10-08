import WeilFixedLineExplicitFormulaContractV2

/-!
AEGIS Ω — preregistered integration contract for the #507 fixed-line RH lane.

The adopted #490 proof route is fixed-line / paired-Hadamard, not a moving
contour shift.  Therefore this contract requires the already proved
multiplicity-weighted zero summability, the actual autocorrelation closure,
the prime-line identity, and the endpoint/pole binding.  It deliberately has
no horizontal-segment-vanishing premise.

RH, the whole explicit formula, and the arithmetic sign remain open.
-/

#check weil_autocorrelation_zero_residue_summable_v2
#check weil_autocorrelation_zero_residue_norm_summable_v2
#check weil_autocorrelation_prime_line_identity_v2
#check WeilAutocorrelationFixedLineReadinessV2
#check weil_autocorrelation_fixed_line_readiness_v2
#check weil_autocorrelation_fixed_line_readiness_of_moments_v2

#check WeilPoleTerm.neg_logDeriv_riemannZeta_residue_one
#check WeilPoleTerm.weil_pole_term_v1
#check WeilPoleTerm.vonMangoldt_lseries_eq_neg_logDeriv_v1

example (g : WeilCompactSmoothGV1) :
    Summable (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g)) :=
  weil_autocorrelation_zero_residue_summable_v2 g

example (g : WeilCompactSmoothGV1) :
    WeilExplicitRightSideConvergentV1 (WeilAutocorrelationV1 g) :=
  (weil_autocorrelation_fixed_line_readiness_v2 g).rhs_convergent

example (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 = 0 :=
  (weil_autocorrelation_fixed_line_readiness_of_moments_v2 g hm).2
