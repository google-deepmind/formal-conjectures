import Bridge
import Main
import Solution.Candidate

open Filter ZetaZeros

/-- DeepMind's distinct-zero question, using Knausgård's dyadic lower bound and the
Alpöge RH theorem. The numerical witness in the bridge is exactly 17/20. -/
theorem riemannZeta.distinct_prop_lt : ∃ c > (3 - montgomeryTaylorConst⁻¹) / 2,
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧ ∀ T > 0,
      (c - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) :=
  DistinctZeros.distinct_prop_lt_of_record riemannHypothesis
    (by norm_num [candidateKappa]) candidate_critical_line_bound

#print axioms riemannZeta.distinct_prop_lt
