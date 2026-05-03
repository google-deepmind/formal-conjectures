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

import FormalConjectures.Util.DeclName
import FormalConjectures.Arxiv.«1308.0994».BoxdotConjecture
import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
import FormalConjectures.Arxiv.«2602.05192».FirstProof4
import FormalConjectures.ErdosProblems.«1038»
import FormalConjectures.ErdosProblems.«1052»
import FormalConjectures.ErdosProblems.«1054»
import FormalConjectures.ErdosProblems.«1063»
import FormalConjectures.ErdosProblems.«1067»
import FormalConjectures.ErdosProblems.«1074»
import FormalConjectures.ErdosProblems.«1142»
import FormalConjectures.ErdosProblems.«12»
import FormalConjectures.ErdosProblems.«141»
import FormalConjectures.ErdosProblems.«17»
import FormalConjectures.ErdosProblems.«198»
import FormalConjectures.ErdosProblems.«263»
import FormalConjectures.ErdosProblems.«26»
import FormalConjectures.ErdosProblems.«295»
import FormalConjectures.ErdosProblems.«317»
import FormalConjectures.ErdosProblems.«349»
import FormalConjectures.ErdosProblems.«350»
import FormalConjectures.ErdosProblems.«36»
import FormalConjectures.ErdosProblems.«392»
import FormalConjectures.ErdosProblems.«399»
import FormalConjectures.ErdosProblems.«41»
import FormalConjectures.ErdosProblems.«42»
import FormalConjectures.ErdosProblems.«442»
import FormalConjectures.ErdosProblems.«457»
import FormalConjectures.ErdosProblems.«494»
import FormalConjectures.ErdosProblems.«503»
import FormalConjectures.ErdosProblems.«50»
import FormalConjectures.ErdosProblems.«513»
import FormalConjectures.ErdosProblems.«56»
import FormalConjectures.ErdosProblems.«590»
import FormalConjectures.ErdosProblems.«617»
import FormalConjectures.ErdosProblems.«61»
import FormalConjectures.ErdosProblems.«678»
import FormalConjectures.ErdosProblems.«686»
import FormalConjectures.ErdosProblems.«697»
import FormalConjectures.ErdosProblems.«835»
import FormalConjectures.ErdosProblems.«865»
import FormalConjectures.ErdosProblems.«886»
import FormalConjectures.ErdosProblems.«920»
import FormalConjectures.ErdosProblems.«951»
import FormalConjectures.ErdosProblems.«965»
import FormalConjectures.ErdosProblems.«968»
import FormalConjectures.ErdosProblems.«985»
import FormalConjectures.GreensOpenProblems.«14»
import FormalConjectures.GreensOpenProblems.«29»
import FormalConjectures.GreensOpenProblems.«32»
import FormalConjectures.Mathoverflow.«10799»
import FormalConjectures.Mathoverflow.«75792»
import FormalConjectures.OEIS.«228828»
import FormalConjectures.OEIS.«231201»
import FormalConjectures.OEIS.«232174»
import FormalConjectures.OEIS.«280831»
import FormalConjectures.OEIS.«56777»
import FormalConjectures.OEIS.«63880»
import FormalConjectures.OEIS.«6697»
import FormalConjectures.OEIS.«67720»
import FormalConjectures.OpenQuantumProblems.«13»
import FormalConjectures.OpenQuantumProblems.«23»
import FormalConjectures.OpenQuantumProblems.«35»
import FormalConjectures.Paper.DegreeSequencesTriangleFree
import FormalConjectures.Paper.Gourevitch
import FormalConjectures.Paper.MonochromaticQuantumGraph
import FormalConjectures.Wikipedia.AgohGiuga
import FormalConjectures.Wikipedia.BealConjecture
import FormalConjectures.Wikipedia.BusyBeaver
import FormalConjectures.Wikipedia.CongruentNumber
import FormalConjectures.Wikipedia.Hadamard
import FormalConjectures.Wikipedia.InverseGalois
import FormalConjectures.Wikipedia.Kaplansky
import FormalConjectures.Wikipedia.LychrelNumbers
import FormalConjectures.Wikipedia.Mahler32
import FormalConjectures.Wikipedia.Pell
import FormalConjectures.Wikipedia.RamanujanTau
import FormalConjectures.Wikipedia.RiemannZetaValues
import FormalConjectures.WrittenOnTheWallII.GraphConjecture13
import FormalConjectures.WrittenOnTheWallII.GraphConjecture16
import FormalConjectures.WrittenOnTheWallII.GraphConjecture33
import FormalConjectures.WrittenOnTheWallII.Test

/-!
# FC100Solved

A random subset of 100 non-open problems, drawn uniformly at random
from all problems without the `category research open` tag
(solved, test, API, etc.).
-/

namespace Subsets.FC100Solved

open Lean in
def problems : List Name := [
  decl_name% WrittenOnTheWallII.Test.petersen_size,
  decl_name% WrittenOnTheWallII.GraphConjecture13.conjecture13,
  decl_name% OpenQuantumProblem35.ame_3_exists,
  decl_name% LychrelNumbers.eventually_palindrome_base10,
  decl_name% Erdos42.example_maximal_sidon,
  decl_name% Mathoverflow75792.Reachable.complexity,
  decl_name% OeisA280831.hasSquareCondition_0,
  decl_name% Erdos141.first_three_odd_primes,
  decl_name% WrittenOnTheWallII.GraphConjecture33.conjecture33,
  decl_name% MonochromaticQuantumGraph.eqSystem4_has_solution_d2,
  decl_name% OeisA228828.a_two,
  decl_name% Erdos399.erdos_399.variants.cambie,
  decl_name% Erdos349.exists_t_for_k_disjoint_segments,
  decl_name% Erdos686.erdos_686.variants.four_three,
  decl_name% OpenQuantumProblem23.hasConstantOverlapSq_singleton,
  decl_name% WrittenOnTheWallII.Test.house_radius,
  decl_name% Erdos678.lcmInterval_lt_example3,
  decl_name% Gourevitch.gourevitch_series_identity,
  decl_name% WrittenOnTheWallII.GraphConjecture16.conjecture16,
  decl_name% Erdos12.erdos_12.variants.erdos_sarkozy,
  decl_name% Mahler32.mahler_conjecture.variants.consequence,
  decl_name% DegreeSequencesTriangleFree.lemma2_d,
  decl_name% Kaplansky.UnitConjecture.counterexamples.ii,
  decl_name% Erdos697.erdos_697.parts.i,
  decl_name% Erdos61.erdos_61.variants.bnss23,
  decl_name% Erdos968.erdos_968.variants.sum_abs_diff_isTheta_log_sq,
  decl_name% RamanujanTau.ramanujan_petersson,
  decl_name% Green14.green_14_quadratic,
  decl_name% Erdos1063.erdos_1063.variants.cambie_upper_bound,
  decl_name% WrittenOnTheWallII.Test.petersen_residue,
  decl_name% Erdos697.density_exists,
  decl_name% Green14.W_3_15,
  decl_name% OpenQuantumProblem35.ame_2_exists,
  decl_name% Erdos392.erdos_392.variants.implication,
  decl_name% Erdos886.erdos_886.variants.rosenfeld_infinite,
  decl_name% OpenQuantumProblem23.qubitSICFamily_pairwise,
  decl_name% Erdos835.johnsonGraph_18_9_chromaticNumber,
  decl_name% OeisA56777.a_65,
  decl_name% Erdos41.erdos_41.variants.pairwise,
  decl_name% OeisA232174.hasPrimeRepresentation_2,
  decl_name% Erdos350.distinctSubsetSums_1_2,
  decl_name% Arxiv.«2602.05192».finiteAdditiveConvolution_monic',
  decl_name% Erdos295.erdos_295.variants.erdos_straus,
  decl_name% Erdos36.M_four,
  decl_name% Erdos590.erdos_590,
  decl_name% Arxiv.«1308.0994».KTExtendsK,
  decl_name% Erdos198.erdos_198.variants.concrete,
  decl_name% Erdos513.erdos_513.variants.lower_bound,
  decl_name% Erdos198.baumgartner_strong,
  decl_name% Erdos617.erdos_617.variants.r_eq_4,
  decl_name% Erdos1038.erdos_1038.parts.ii,
  decl_name% OeisA231201.primeCondition_8,
  decl_name% Erdos56.maxWeaklyDivisible_one,
  decl_name% Erdos17.isClusterPrime_97_isLeast_non_cluster,
  decl_name% BealConjecture.flt_of_beal_conjecture,
  decl_name% Arxiv.«1609.08688».maximalLength_ge_of_isSquare,
  decl_name% RiemannZetaValues.infinite_irrational_at_odd,
  decl_name% AgohGiuga.isWeakGiuga_iff_sum_primeFactors,
  decl_name% OeisA6697.count_false_morphism,
  decl_name% Mathoverflow10799.μ_half_eq_uniform,
  decl_name% OeisA67720.a_6,
  decl_name% OpenQuantumProblem13.Qubit.star_smul_mul_smul,
  decl_name% Erdos920.erdos_920.variants.k_eq_3,
  decl_name% Erdos26.erdos_26.variants.rusza,
  decl_name% InverseGalois.inverse_galois_problem.variants.symmetric_group,
  decl_name% Erdos1067.erdos_1067.variants.infinite_edge_connectivity,
  decl_name% Erdos1074.erdos_1074.variants.EHSNumbers_init,
  decl_name% Erdos26.not_isThick_of_finite,
  decl_name% Erdos50.erdos_50_schoenberg,
  decl_name% Erdos951.erdos_951.variants.isBeurlingPrimes,
  decl_name% Erdos965.erdos_965.variants.generalization,
  decl_name% Erdos985.erdos_985.variants.two_three_five_primitive_root,
  decl_name% PellNumbers.pellNumber_two,
  decl_name% WrittenOnTheWallII.Test.C6_size,
  decl_name% BusyBeaver.sanity_check,
  decl_name% OpenQuantumProblem13.Qubit.firstCol_normSq,
  decl_name% Erdos263.erdos_263.variants.sub_doubly_exponential,
  decl_name% Arxiv.«1609.08688».tripleProduct_const,
  decl_name% Erdos317.erdos_317.variants.counterexample,
  decl_name% OpenQuantumProblem23.sicOverlapSq_three,
  decl_name% Erdos442.erdos_442.variants.tao,
  decl_name% AgohGiuga.korselts_criterion,
  decl_name% Erdos1054.f_undefined_at_2,
  decl_name% Erdos503.erdos_503.variants.R3,
  decl_name% OeisA63880.a_of_primitive_mul_squarefree,
  decl_name% Erdos1142.erdos_1142.variants.mientka_weitzenkamp,
  decl_name% CongruentNumber.congruentNumber_7,
  decl_name% WrittenOnTheWallII.Test.petersen_szeged,
  decl_name% WrittenOnTheWallII.Test.petersen_radius,
  decl_name% Erdos590.erdos_590.variants.ge_three_false,
  decl_name% Erdos494.erdos_494.variants.product,
  decl_name% Green29.green_29.variant,
  decl_name% Erdos865.erdos_865.variants.k2,
  decl_name% Hadamard.HadamardConjecture.variants.first_cases,
  decl_name% Mathoverflow10799.boundaryCount_univ,
  decl_name% Erdos457.erdos_457,
  decl_name% OpenQuantumProblem23.bb84Family_not_isSICFamily,
  decl_name% Green32.hasGap_empty,
  decl_name% Erdos1052.isUnitaryPerfect_60,
  decl_name% OeisA67720.a_1
]

end Subsets.FC100Solved

open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100Solved.problems [
  ("test", 34),
  ("research solved", 50),
  ("API", 9),
  ("textbook", 7)
]
