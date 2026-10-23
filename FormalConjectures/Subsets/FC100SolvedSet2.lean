/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil.DeclName
public import FormalConjecturesUtil
public import FormalConjectures.Arxiv.«0805.3777».TensorRank
public import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
public import FormalConjectures.Arxiv.«2001.02665».RingelConjecture
public import FormalConjectures.Arxiv.«2208.14736».ZariskiCancellation
public import FormalConjectures.Arxiv.«2504.17644».Margulis
public import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles
public import FormalConjectures.Arxiv.«math.0301027».FiniteGenerationOfCohomology
public import FormalConjectures.Arxiv.«math.0608009».DixmierConjecture
public import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_32
public import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6
public import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8
public import FormalConjectures.ErdosProblems.«1057»
public import FormalConjectures.ErdosProblems.«114»
public import FormalConjectures.ErdosProblems.«325»
public import FormalConjectures.ErdosProblems.«408»
public import FormalConjectures.ErdosProblems.«507»
public import FormalConjectures.ErdosProblems.«5»
public import FormalConjectures.ErdosProblems.«604»
public import FormalConjectures.ErdosProblems.«61»
public import FormalConjectures.ErdosProblems.«65»
public import FormalConjectures.ErdosProblems.«687»
public import FormalConjectures.ErdosProblems.«723»
public import FormalConjectures.ErdosProblems.«813»
public import FormalConjectures.ErdosProblems.«89»
public import FormalConjectures.ErdosProblems.«940»
public import FormalConjectures.ErdosProblems.«985»
public import FormalConjectures.GreensOpenProblems.«14»
public import FormalConjectures.GreensOpenProblems.«16»
public import FormalConjectures.GreensOpenProblems.«18»
public import FormalConjectures.GreensOpenProblems.«19»
public import FormalConjectures.GreensOpenProblems.«21»
public import FormalConjectures.GreensOpenProblems.«22»
public import FormalConjectures.GreensOpenProblems.«26»
public import FormalConjectures.GreensOpenProblems.«27»
public import FormalConjectures.GreensOpenProblems.«29»
public import FormalConjectures.GreensOpenProblems.«2»
public import FormalConjectures.GreensOpenProblems.«31»
public import FormalConjectures.GreensOpenProblems.«41»
public import FormalConjectures.GreensOpenProblems.«4»
public import FormalConjectures.GreensOpenProblems.«51»
public import FormalConjectures.GreensOpenProblems.«54»
public import FormalConjectures.GreensOpenProblems.«72»
public import FormalConjectures.GreensOpenProblems.«82»
public import FormalConjectures.GreensOpenProblems.«9»
public import FormalConjectures.HilbertProblems.«5»
public import FormalConjectures.Kourovka.«1_74»
public import FormalConjectures.Kourovka.«8_8»
public import FormalConjectures.LittProblems.«1»
public import FormalConjectures.Millennium.Poincare
public import FormalConjectures.OEIS.«109074»
public import FormalConjectures.Other.HyperbolicGroupsResiduallyFinite
public import FormalConjectures.Other.SymbolLengthMilnorKTheory
public import FormalConjectures.Paper.AuslanderReiten
public import FormalConjectures.Paper.ConjugacyClassSizes
public import FormalConjectures.Paper.DeGiorgi
public import FormalConjectures.Paper.EisenbudGreenHarris
public import FormalConjectures.Paper.FiniteLocallyFreeGroupSchemeExponent
public import FormalConjectures.Paper.Gourevitch
public import FormalConjectures.Paper.KaplanskyUInvariant
public import FormalConjectures.Paper.RiemannHypothesisEquivalents
public import FormalConjectures.Paper.RiemannZetaMoments
public import FormalConjectures.Paper.ShelahSpencerZeroOneLaw
public import FormalConjectures.Paper.WeaklyFirstCountable
public import FormalConjectures.Paper.ZagierMZV
public import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
public import FormalConjectures.Wikipedia.Bloch
public import FormalConjectures.Wikipedia.CarmichaelTotient
public import FormalConjectures.Wikipedia.ClassNumberProblem
public import FormalConjectures.Wikipedia.CongruentNumber
public import FormalConjectures.Wikipedia.DiophantineTuple
public import FormalConjectures.Wikipedia.DirichletDivisorProblem
public import FormalConjectures.Wikipedia.ElliottHalberstamConjecture
public import FormalConjectures.Wikipedia.EllipticCurveRank
public import FormalConjectures.Wikipedia.FermatCatalanConjecture
public import FormalConjectures.Wikipedia.GaussCircleProblem
public import FormalConjectures.Wikipedia.GromovPolynomialGrowth
public import FormalConjectures.Wikipedia.HasseWeil
public import FormalConjectures.Wikipedia.InscribedSquare
public import FormalConjectures.Wikipedia.InverseGalois
public import FormalConjectures.Wikipedia.Kakeya
public import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem
public import FormalConjectures.Wikipedia.LocalUniformization
public import FormalConjectures.Wikipedia.LonelyRunnerConjecture
public import FormalConjectures.Wikipedia.Mahler32
public import FormalConjectures.Wikipedia.Mills
public import FormalConjectures.Wikipedia.NoetherProblem
public import FormalConjectures.Wikipedia.PerfectNumbers
public import FormalConjectures.Wikipedia.PierceBirkhoff
public import FormalConjectures.Wikipedia.PowerfulNumbersDensity
public import FormalConjectures.Wikipedia.RamanujanTau
public import FormalConjectures.Wikipedia.RamseyNumbers
public import FormalConjectures.Wikipedia.ResolutionOfSingularities
public import FormalConjectures.Wikipedia.RiemannZetaValues
public import FormalConjectures.Wikipedia.SatoTateConjecture
public import FormalConjectures.Wikipedia.SerreMultiplicityConjectures
public import FormalConjectures.Wikipedia.SixStandardDeviations
public import FormalConjectures.Wikipedia.SmallCohenMacaulayModules
public import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem
public import FormalConjectures.Wikipedia.Transcendental
public import FormalConjectures.Wikipedia.UnionClosed

/-!
# FC100SolvedSet2

A curated subset of 100 hard-to-formalise solved research problems with verified
formal statements (`category research solved`) and no existing formal proof.
-/

@[expose] public section

set_option linter.style.imports false

namespace Subsets.FC100SolvedSet2

open Lean in
def problems : List Name := [
  decl_name% PoincareConjecture.poincare_conjecture.variants.smooth_known_cases,
  decl_name% SatoTateConjecture.satoTate_conjecture,
  decl_name% HasseWeil.exists_hasAnalyticContinuation_rat,
  decl_name% AlgebraicGeometry.resolution_of_singularities_of_topologicalKrullDim_le_three,
  decl_name% RamanujanTau.ramanujan_petersson,
  decl_name% FermatCatalanConjecture.fermat_catalan.variants.darmon_granville,
  decl_name% Hilbert5.hilbert_smith_conjecture.variants.dimension_three,
  decl_name% SmallCohenMacaulayModules.exists_isBalancedBigCohenMacaulay,
  decl_name% EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le,
  decl_name% SerreMultiplicityConjectures.intersectionMultiplicity_eq_zero_of_lt,
  decl_name% Erdos89.erdos_89.variants.n_dvd_log_n,
  decl_name% Bugeaud08.problem_10_8.variants.exceptional_set_dimH_zero,
  decl_name% Bugeaud32.adamczewski_faverjon,
  decl_name% ZagierMZV.zagier_upper_bound,
  decl_name% DeGiorgi.DeGiorgi_ge_nine,
  decl_name% Erdos325.erdos_325.variants.wooley,
  decl_name% Erdos507.erdos_507.variants.upper_cpz24,
  decl_name% Erdos65.erdos_65.variants.liu_montgomery,
  decl_name% GromovPolynomialGrowth.GromovPolynomialGrowthTheorem,
  decl_name% Erdos687.erdos_687.variants.fgkmt,
  decl_name% SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt,
  decl_name% Erdos723.erdos_723.variants.leq_11,
  decl_name% KaplanskyUInvariant.u_invariant_values.variants.two_pow_add_one,
  decl_name% Kourovka.«1.74».kourovka_1_74.variants.tarski_monster,
  decl_name% LocalUniformization.local_uniformization_of_trdeg_le_three,
  decl_name% TarskiExponentialFunctionProblem.isDecidable_completeTheory_realExp_of_realSchanuelConjecture,
  decl_name% Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_two,
  decl_name% Erdos1057.erdos_1057.variants.agp_lower_bound,
  decl_name% Kakeya.kakeya_3d,
  decl_name% Erdos114.erdos_114.variants.large_n,
  decl_name% CongruentNumber.Tunnell_even,
  decl_name% PerfectNumbers.odd_perfect_number.lower_bound,
  decl_name% ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.variants.part_ii_power_squarefreePart_not_modeq_one,
  decl_name% Erdos5.erdos_5.variants.merikoski_measure,
  decl_name% HopfAlgebraCohomology.cohomology_finite_of_isCocomm,
  decl_name% Green9.green_9_i,
  decl_name% Arxiv.«2001.02665».kotzig_conjecture_large,
  decl_name% Erdos940.erdos_940.variants.three_powerful,
  decl_name% ClassNumberProblem.class_number_problem.variants.imaginary,
  decl_name% ElliottHalberstamConjecture.elliott_halberstam.variants.friedlander_granville,
  decl_name% Erdos813.erdos_813.variants.bucic_sudakov,
  decl_name% Mills.exists_least,
  decl_name% RamseyNumbers.ramsey_number_five_five_upper_bound,
  decl_name% Transcendental.transcendental_gamma_one_div_three,
  decl_name% Erdos61.erdos_61.variants.bnss23,
  decl_name% Erdos985.erdos_985.variants.two_three_five_primitive_root,
  decl_name% Green41.minCopies_set_nonempty,
  decl_name% RiemannZetaMoments.moment_isEquiv₂,
  decl_name% Erdos604.erdos_604.variants.katz_tardos,
  decl_name% Erdos408.erdos_408.variants.ford_konyagin_luca,
  decl_name% Green4.large_green_4,
  decl_name% InverseGalois.inverse_galois_problem.variants.complex_rational_functions,
  decl_name% Margulis.huang_shi_theorem_1_2,
  decl_name% DiophantineTuple.noIntegralDiophantineFiveTuple,
  decl_name% PierceBirkhoff.pierce_birkhoff_conjecture_dim_two,
  decl_name% ShelahSpencerZeroOneLaw.zeroOne_irrational,
  decl_name% LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017,
  decl_name% RiemannHypothesis.weil_positivity_criterion,
  decl_name% Green14.green_14_polynomial_k_eq_3,
  decl_name% Green22.green_22.variants.moreira_infinite,
  decl_name% Arxiv.«0805.3777».isGenericRank_cube,
  decl_name% Arxiv.«2606.03696».bondy_conjecture.variants.large_explicit,
  decl_name% Green2.green_2_lower_bound_sanders,
  decl_name% RiemannZetaValues.infinite_irrational_at_odd,
  decl_name% CarmichaelTotient.carchimaelTotient_bound,
  decl_name% HyperbolicGroupsResiduallyFinite.hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top,
  decl_name% Kourovka.«8.8».kourovka_8_8a,
  decl_name% EisenbudGreenHarris.eisenbud_green_harris.variants.caviglia_deStefani,
  decl_name% Arxiv.«math.0608009».dixmier_conjecture.variants.poisson_implication,
  decl_name% AuslanderReiten.auslander_reiten.variants.normal,
  decl_name% Green19.green_19,
  decl_name% Green54.green_54,
  decl_name% Green72.no_k_in_line_big,
  decl_name% InscribedSquare.exists_inscribed_square_of_C2,
  decl_name% OeisA109074.conjecture,
  decl_name% DirichletDivisorProblem.divisor_error_hardy,
  decl_name% Green16.green_16_upper_bound,
  decl_name% PowerfulNumbersDensity.asymptotic_bateman_grosswald,
  decl_name% NoetherProblem.noether_problem.variants.forty_seven,
  decl_name% UnionClosed.union_closed.variants.yu,
  decl_name% GaussCircleProblem.error_not_isLittleO,
  decl_name% Arxiv.«1609.08688».maximalLength_le_isBigO,
  decl_name% Bloch.landauConstant_upper_bound,
  decl_name% Green26.green_26.variants.yu25,
  decl_name% Green27.green_27.variants.lower_be23,
  decl_name% LamLitt.lam_litt.variants.eisenstein,
  decl_name% Mahler32.mahler_conjecture.variants.flatto_lagarias_pollington,
  decl_name% FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.reduced_base,
  decl_name% Green18.green_18.bmz_corners,
  decl_name% Gourevitch.gourevitch_series_identity,
  decl_name% ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable,
  decl_name% Green82.green_82_upper_bound,
  decl_name% Bugeaud06.boshernitzan,
  decl_name% Green29.green_29.variant,
  decl_name% Green31.green_31.variants.upper_cho25,
  decl_name% WeaklyFirstCountable.CH.existsWeaklyFirstCountableCompactNotFirstCountable,
  decl_name% Green21.green_21.variants.fox_kleitman,
  decl_name% Green51.green_51.upper_ap,
  decl_name% LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.not_reciprocal,
  decl_name% SixStandardDeviations.six_standard_deviations
]

end Subsets.FC100SolvedSet2

open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100SolvedSet2.problems [
  ("research solved", 100)
]
