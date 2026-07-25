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
public import FormalConjectures.Arxiv.«0912.2382».CurlingNumberConjecture
public import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents
public import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS
public import FormalConjectures.Books.UniformDistributionOfSequences.Equidistribution
public import FormalConjectures.ErdosProblems.«1002»
public import FormalConjectures.ErdosProblems.«1074»
public import FormalConjectures.ErdosProblems.«1092»
public import FormalConjectures.ErdosProblems.«1093»
public import FormalConjectures.ErdosProblems.«1097»
public import FormalConjectures.ErdosProblems.«1113»
public import FormalConjectures.ErdosProblems.«123»
public import FormalConjectures.ErdosProblems.«125»
public import FormalConjectures.ErdosProblems.«12»
public import FormalConjectures.ErdosProblems.«137»
public import FormalConjectures.ErdosProblems.«188»
public import FormalConjectures.ErdosProblems.«200»
public import FormalConjectures.ErdosProblems.«23»
public import FormalConjectures.ErdosProblems.«260»
public import FormalConjectures.ErdosProblems.«269»
public import FormalConjectures.ErdosProblems.«272»
public import FormalConjectures.ErdosProblems.«282»
public import FormalConjectures.ErdosProblems.«288»
public import FormalConjectures.ErdosProblems.«307»
public import FormalConjectures.ErdosProblems.«313»
public import FormalConjectures.ErdosProblems.«324»
public import FormalConjectures.ErdosProblems.«329»
public import FormalConjectures.ErdosProblems.«332»
public import FormalConjectures.ErdosProblems.«340»
public import FormalConjectures.ErdosProblems.«358»
public import FormalConjectures.ErdosProblems.«36»
public import FormalConjectures.ErdosProblems.«385»
public import FormalConjectures.ErdosProblems.«398»
public import FormalConjectures.ErdosProblems.«409»
public import FormalConjectures.ErdosProblems.«479»
public import FormalConjectures.ErdosProblems.«517»
public import FormalConjectures.ErdosProblems.«535»
public import FormalConjectures.ErdosProblems.«539»
public import FormalConjectures.ErdosProblems.«61»
public import FormalConjectures.ErdosProblems.«647»
public import FormalConjectures.ErdosProblems.«694»
public import FormalConjectures.ErdosProblems.«695»
public import FormalConjectures.ErdosProblems.«770»
public import FormalConjectures.ErdosProblems.«830»
public import FormalConjectures.ErdosProblems.«887»
public import FormalConjectures.ErdosProblems.«888»
public import FormalConjectures.ErdosProblems.«890»
public import FormalConjectures.ErdosProblems.«92»
public import FormalConjectures.ErdosProblems.«931»
public import FormalConjectures.ErdosProblems.«952»
public import FormalConjectures.ErdosProblems.«996»
public import FormalConjectures.GreensOpenProblems.«14»
public import FormalConjectures.GreensOpenProblems.«24»
public import FormalConjectures.GreensOpenProblems.«31»
public import FormalConjectures.GreensOpenProblems.«58»
public import FormalConjectures.GreensOpenProblems.«61»
public import FormalConjectures.GreensOpenProblems.«9»
public import FormalConjectures.Mathoverflow.«1973»
public import FormalConjectures.Millenium.Poincare
public import FormalConjectures.OEIS.«303656»
public import FormalConjectures.OEIS.«308734»
public import FormalConjectures.OEIS.«41»
public import FormalConjectures.OEIS.«63880»
public import FormalConjectures.OEIS.«67720»
public import FormalConjectures.OEIS.«80170»
public import FormalConjectures.OpenQuantumProblems.«23»
public import FormalConjectures.Paper.MonochromaticQuantumGraph
public import FormalConjectures.Wikipedia.Buchi
public import FormalConjectures.Wikipedia.ClassNumberProblem
public import FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups
public import FormalConjectures.Wikipedia.EllipticCurveRank
public import FormalConjectures.Wikipedia.EulerBrick
public import FormalConjectures.Wikipedia.Gilbreath
public import FormalConjectures.Wikipedia.Grimm
public import FormalConjectures.Wikipedia.Irrational
public import FormalConjectures.Wikipedia.Koethe
public import FormalConjectures.Wikipedia.LittlewoodConjecture
public import FormalConjectures.Wikipedia.LychrelNumbers
public import FormalConjectures.Wikipedia.Mandelbrot
public import FormalConjectures.Wikipedia.Pell
public import FormalConjectures.Wikipedia.RamseyNumbers
public import FormalConjectures.Wikipedia.RiemannZetaValues
public import FormalConjectures.Wikipedia.Selfridge
public import FormalConjectures.Wikipedia.SumOfThreeCubes
public import FormalConjectures.Wikipedia.Superperfectnumbers
public import FormalConjectures.Wikipedia.Transcendental
public import FormalConjectures.Wikipedia.UnionClosed
public import FormalConjectures.WrittenOnTheWallII.GraphConjecture316
public import FormalConjectures.WrittenOnTheWallII.GraphConjecture327

/-!
# FC100OpenSet1

A random subset of 100 open research problems, drawn uniformly at random
from all problems with the `category research open` tag.
-/

@[expose] public section

namespace Subsets.FC100OpenSet1

open Lean in
def problems : List Name := [
  decl_name% OeisA308734.conjecture,
  decl_name% Buchi.buchi_problem,
  decl_name% Erdos200.erdos_200,
  decl_name% Green31.green_31.variants.upper_eventually,
  decl_name% Equidistribution.isAccumulationPoint_three_halves_pow,
  decl_name% Koethe.KotherConjecture.variants.matrixOver_KotherRadical,
  decl_name% Erdos535.erdos_535.variants.first_open_case,
  decl_name% LychrelNumbers.no_lychrel_numbers_base10,
  decl_name% Erdos830.erdos_830.parts.ii,
  decl_name% Erdos125.erdos_125.variants.positive_unequal_density,
  decl_name% Erdos1113.erdos_1113.variants.filaseta_finch_kozek,
  decl_name% Erdos539.erdos_539.variants.isBigO_sq,
  decl_name% RiemannZetaValues.irrational_five,
  decl_name% Erdos1074.erdos_1074.parts.ii,
  decl_name% Erdos282.erdos_282.variants.general,
  decl_name% PellNumbers.infinite_pellNumber_primes,
  decl_name% ClassNumberProblem.class_number_problem,
  decl_name% Grimm.grimm_conjecture_weak,
  decl_name% OeisA63880.mod_216_of_a,
  decl_name% Green24.green_24,
  decl_name% Erdos12.erdos_12.parts.iii,
  decl_name% Erdos288.erdos_288.variants.exists_k_gt_2,
  decl_name% EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic,
  decl_name% Erdos647.erdos_647.variants.lim,
  decl_name% Selfridge.selfridge_conjecture,
  decl_name% Erdos887.erdos_887.parts.i,
  decl_name% Erdos340.erdos_340.variants.co_density_zero_sub,
  decl_name% Erdos694.erdos_694.variants.carmichael,
  decl_name% Mathoverflow1973.mathoverflow_1973,
  decl_name% Erdos479.erdos_479,
  decl_name% OeisA67720.prime_add_one_of_a,
  decl_name% Erdos1092.f_asymptotic_general,
  decl_name% Erdos1074.erdos_1074.parts.iv,
  decl_name% Green9.green_9_iii,
  decl_name% Erdos770.erdos_770.variants.three,
  decl_name% Erdos137.erdos_137.variants.multiple_powerful_factors,
  decl_name% Irrational.irrational_e_to_e,
  decl_name% Erdos324.erdos_324,
  decl_name% Erdos329.erdos_329,
  decl_name% Transcendental.pi_pow_pi_pow_pi_transcendental,
  decl_name% Erdos409.erdos_409.parts.i.isBigO,
  decl_name% Arxiv.«2501.03234».conjecture_4_1,
  decl_name% MonochromaticQuantumGraph.eqSystem10_no_solution_d3,
  decl_name% PoincareConjecture.poincare_conjecture.variants.smooth_dimension_four,
  decl_name% Transcendental.pi_pow_sqrt_two_transcendental,
  decl_name% OeisA303656.conjecture,
  decl_name% Erdos517.erdos_517,
  decl_name% MonochromaticQuantumGraph.eqSystem16_no_solution_d3,
  decl_name% Arxiv.«0912.2382».curling_number_conjecture,
  decl_name% Grimm.grimm_conjecture,
  decl_name% Erdos272.erdos_272.variants.szabo_strong,
  decl_name% UnionClosed.union_closed.variants.cardinality_even_of_union_closed_tight,
  decl_name% MonochromaticQuantumGraph.eqSystem12_no_solution_d3,
  decl_name% Erdos1097.erdos_1097,
  decl_name% MonochromaticQuantumGraph.eqSystem_no_solution_ge6_ge3_real,
  decl_name% Erdos952.erdos_952,
  decl_name% Green58.green_58,
  decl_name% Erdos329.erdos_329.variants.converse_implication,
  decl_name% Mandelbrot.MLC,
  decl_name% Erdos890.erdos_890.parts.a,
  decl_name% Erdos1002.erdos_1002,
  decl_name% Erdos188.erdos_188,
  decl_name% BabaiSeressConjectures.babai_seress_conjecture_alternating,
  decl_name% OpenQuantumProblem23.hasSICPOVM_60,
  decl_name% Erdos23.erdos_23,
  decl_name% Gilbreath.gilbreath_conjecture,
  decl_name% Erdos313.erdos_313,
  decl_name% Green14.W_3_39_lower,
  decl_name% Erdos931.erdos_931.variants.exists_prime,
  decl_name% Erdos398.erdos_398,
  decl_name% Erdos61.erdos_61,
  decl_name% Erdos996.erdos_996,
  decl_name% Erdos695.erdos_695,
  decl_name% MonochromaticQuantumGraph.eqSystem10_no_solution_d3_trinary_int,
  decl_name% Erdos92.erdos_92.variants.weak,
  decl_name% RamseyNumbers.ramsey_number_five_five,
  decl_name% Erdos385.erdos_385.parts.ii,
  decl_name% LittlewoodConjecture.padic_littlewood_conjecture,
  decl_name% Mandelbrot.volume_frontier_mandelbrotSet_eq_zero,
  decl_name% Erdos358.erdos_358.variants.prime_set,
  decl_name% OeisA80170.gcdCondition_iff_primePowerCondition,
  decl_name% Erdos332.erdos_332,
  decl_name% Green14.W_3_37_lower,
  decl_name% EulerBrick.cuboidThree,
  decl_name% Erdos269.erdos_269.variants.rational,
  decl_name% Arxiv.«1601.03081».crystals_components_unique,
  decl_name% Erdos123.erdos_123.variants.powers_2_3_5_snug,
  decl_name% SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9,
  decl_name% WrittenOnTheWallII.GraphConjecture327.conjecture327,
  decl_name% WrittenOnTheWallII.GraphConjecture316.conjecture316,
  decl_name% Erdos888.erdos_888,
  decl_name% Erdos260.erdos_260,
  decl_name% Erdos36.erdos_36.variants.lower,
  decl_name% MonochromaticQuantumGraph.eqSystem10_no_solution_d4,
  decl_name% Superperfect.twoFivePerfect,
  decl_name% Erdos307.erdos_307,
  decl_name% MonochromaticQuantumGraph.eqSystem6_no_solution_d4,
  decl_name% OeisA41.noPowerPartitionNumber,
  decl_name% Erdos1093.erdos_1093.parts.ii,
  decl_name% Green61.green_61
]

end Subsets.FC100OpenSet1

open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100OpenSet1.problems [
  ("research open", 94),
  ("research solved", 6)
]
