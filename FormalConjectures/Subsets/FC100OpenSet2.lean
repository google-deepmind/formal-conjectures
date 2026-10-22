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
public import FormalConjectures.Arxiv.«2303.01089».FurstenbergTimesPTimesQ
public import FormalConjectures.Arxiv.«2504.17644».Margulis
public import FormalConjectures.Arxiv.«math.0110202».BanachMazurRotation
public import FormalConjectures.Arxiv.«math.0301027».FiniteGenerationOfCohomology
public import FormalConjectures.Arxiv.«math.0703548».FarrellJonesConsequences
public import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8
public import FormalConjectures.Books.UniformDistributionOfSequences.Equidistribution
public import FormalConjectures.ErdosProblems.«1029»
public import FormalConjectures.ErdosProblems.«107»
public import FormalConjectures.ErdosProblems.«212»
public import FormalConjectures.ErdosProblems.«233»
public import FormalConjectures.ErdosProblems.«234»
public import FormalConjectures.ErdosProblems.«242»
public import FormalConjectures.ErdosProblems.«28»
public import FormalConjectures.ErdosProblems.«510»
public import FormalConjectures.ErdosProblems.«52»
public import FormalConjectures.ErdosProblems.«562»
public import FormalConjectures.ErdosProblems.«564»
public import FormalConjectures.ErdosProblems.«572»
public import FormalConjectures.ErdosProblems.«583»
public import FormalConjectures.ErdosProblems.«5»
public import FormalConjectures.ErdosProblems.«61»
public import FormalConjectures.ErdosProblems.«714»
public import FormalConjectures.ErdosProblems.«723»
public import FormalConjectures.GreensOpenProblems.«50»
public import FormalConjectures.Millennium.BSD
public import FormalConjectures.Millennium.NavierStokes
public import FormalConjectures.Millennium.Poincare
public import FormalConjectures.Millennium.PvsNP
public import FormalConjectures.Millennium.RiemannHypothesis
public import FormalConjectures.OpenQuantumProblems.«23»
public import FormalConjectures.Paper.ReedOmegaDeltaChi
public import FormalConjectures.Paper.SerreUniformity
public import FormalConjectures.Paper.ZagierMZV
public import FormalConjectures.Wikipedia.ABC
public import FormalConjectures.Wikipedia.AlgebraicNormality
public import FormalConjectures.Wikipedia.AndrewsCurtis
public import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
public import FormalConjectures.Wikipedia.BatemanHornConjecture
public import FormalConjectures.Wikipedia.BealConjecture
public import FormalConjectures.Wikipedia.BeckFialaConjecture
public import FormalConjectures.Wikipedia.BingBorsuk
public import FormalConjectures.Wikipedia.Bloch
public import FormalConjectures.Wikipedia.Bunyakovsky
public import FormalConjectures.Wikipedia.Catalan
public import FormalConjectures.Wikipedia.ClassNumberProblem
public import FormalConjectures.Wikipedia.CollatzConjecture
public import FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups
public import FormalConjectures.Wikipedia.Dickson
public import FormalConjectures.Wikipedia.ElliottHalberstamConjecture
public import FormalConjectures.Wikipedia.EllipticCurveRank
public import FormalConjectures.Wikipedia.Exponentials
public import FormalConjectures.Wikipedia.Fermat
public import FormalConjectures.Wikipedia.FermatCatalanConjecture
public import FormalConjectures.Wikipedia.FibonacciPrimes
public import FormalConjectures.Wikipedia.GapConjecture
public import FormalConjectures.Wikipedia.GaussCircleProblem
public import FormalConjectures.Wikipedia.GoldbachConjecture
public import FormalConjectures.Wikipedia.Hadamard
public import FormalConjectures.Wikipedia.Hall
public import FormalConjectures.Wikipedia.HardyLittlewood
public import FormalConjectures.Wikipedia.HasseWeil
public import FormalConjectures.Wikipedia.IdonealCompleteness
public import FormalConjectures.Wikipedia.InscribedSquare
public import FormalConjectures.Wikipedia.IntegerFactorization
public import FormalConjectures.Wikipedia.InvariantSubspaceProblem
public import FormalConjectures.Wikipedia.InverseGalois
public import FormalConjectures.Wikipedia.Irrational
public import FormalConjectures.Wikipedia.JacobianConjecture
public import FormalConjectures.Wikipedia.Jacobson
public import FormalConjectures.Wikipedia.Kakeya
public import FormalConjectures.Wikipedia.KummerVandiver
public import FormalConjectures.Wikipedia.LegendreConjecture
public import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem
public import FormalConjectures.Wikipedia.LittlewoodConjecture
public import FormalConjectures.Wikipedia.LocalUniformization
public import FormalConjectures.Wikipedia.LonelyRunnerConjecture
public import FormalConjectures.Wikipedia.Mandelbrot
public import FormalConjectures.Wikipedia.Mersenne
public import FormalConjectures.Wikipedia.PerfectNumbers
public import FormalConjectures.Wikipedia.PierceBirkhoff
public import FormalConjectures.Wikipedia.PrimeTriplets
public import FormalConjectures.Wikipedia.PrimesAndPerfectSquares
public import FormalConjectures.Wikipedia.RamanujanTau
public import FormalConjectures.Wikipedia.RegularPrimes
public import FormalConjectures.Wikipedia.ResolutionOfSingularities
public import FormalConjectures.Wikipedia.RiemannZetaValues
public import FormalConjectures.Wikipedia.RudinsConjecture
public import FormalConjectures.Wikipedia.Schanuel
public import FormalConjectures.Wikipedia.Schinzel
public import FormalConjectures.Wikipedia.Singmaster
public import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem
public import FormalConjectures.Wikipedia.Transcendental
public import FormalConjectures.Wikipedia.TwinPrimes
public import FormalConjectures.Wikipedia.UnionClosed
public import FormalConjectures.Wikipedia.VaughtConjecture
public import FormalConjectures.Wikipedia.conjecture_1_3_to_2_3

/-!
# FC100OpenSet2

A curated subset of 100 mathematically important open research conjectures with
verified formal statements (`category research open`), excluding sub-variants,
OEIS sequences, and machine-generated graph conjectures.
-/

@[expose] public section

set_option linter.style.imports false

namespace Subsets.FC100OpenSet2

open Lean in
def problems : List Name := [
  decl_name% RiemannHypothesis.riemannHypothesis,
  decl_name% ComplexityTheory.P_ne_NP,
  decl_name% GRH.generalized_riemann_hypothesis,
  decl_name% WeierstrassCurve.Affine.NumberField.weakBSD,
  decl_name% NavierStokes.navier_stokes_existence_and_smoothness_R3,
  decl_name% ABC.abc,
  decl_name% AlgebraicGeometry.resolution_of_singularities,
  decl_name% GoldbachConjecture.goldbach,
  decl_name% InverseGalois.inverse_galois_problem,
  decl_name% PoincareConjecture.poincare_conjecture.variants.smooth_dimension_four,
  decl_name% TwinPrimes.twin_primes,
  decl_name% Kakeya.kakeya_set_conjecture,
  decl_name% ComplexityTheory.NP_ne_coNP,
  decl_name% Schinzel.schinzel_conjecture,
  decl_name% HardyLittlewood.first_hardy_littlewood_conjecture,
  decl_name% Mandelbrot.MLC,
  decl_name% LittlewoodConjecture.littlewood_conjecture,
  decl_name% HasseWeil.exists_hasAnalyticContinuation,
  decl_name% Schanuel.schanuel_conjecture,
  decl_name% Dickson.dickson_conjecture,
  decl_name% InvariantSubspaceProblem.Invariant_subspace_problem,
  decl_name% EllipticCurveRank.RatEllipticCurve.unbounded_rank_conjecture,
  decl_name% BatemanHornConjecture.bateman_horn_conjecture,
  decl_name% LocalUniformization.local_uniformization,
  decl_name% ElliottHalberstamConjecture.elliott_halberstam,
  decl_name% Arxiv.«math.0703548».projective_module_isStablyFree,
  decl_name% Erdos61.erdos_61,
  decl_name% SerreUniformity.serre_uniformity,
  decl_name% ClassNumberProblem.class_number_problem,
  decl_name% Arxiv.id2303_01089.conjecture_1_3,
  decl_name% Irrational.algebraicIndependent_e_pi,
  decl_name% Bunyakovsky.bunyakovsky_conjecture,
  decl_name% Erdos52.erdos_52,
  decl_name% PolyTime.isPolyTime_primeFactorsList,
  decl_name% ZagierMZV.zagier_conjecture,
  decl_name% LegendreConjecture.legendre_conjecture,
  decl_name% KummerVandiver.kummer_vandiver,
  decl_name% RegularPrimes.regularprime_conjecture,
  decl_name% JacobianConjecture.jacobian_conjecture_two_variables,
  decl_name% ArtinPrimitiveRootsConjecture.artin_primitive_roots.parts.i,
  decl_name% Catalan.pillais_conjecture,
  decl_name% Hadamard.HadamardConjecture,
  decl_name% VaughtConjecture.vaught_conjecture,
  decl_name% AlgebraicNormality.irrational_algebraic_absolutely_normal,
  decl_name% LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem,
  decl_name% RiemannZetaValues.irrational_odd,
  decl_name% BeckFiala.beck_fiala_conjecture,
  decl_name% RamanujanTau.lehmer_ramanujan_tau,
  decl_name% UnionClosed.union_closed,
  decl_name% Erdos28.erdos_28,
  decl_name% GaussCircleProblem.error_isBigO,
  decl_name% PrimesAndPerfectSquares.infinite_prime_sq_add_one,
  decl_name% BabaiSeressConjectures.babai_seress_conjecture,
  decl_name% TarskiExponentialFunctionProblem.tarski_exponential_function_problem,
  decl_name% Margulis.conjecture_1_1,
  decl_name% Exponentials.four_exponentials_conjecture,
  decl_name% HopfAlgebraCohomology.cohomologyRing_finiteType,
  decl_name% Erdos723.erdos_723,
  decl_name% AndrewsCurtis.andrews_curtis_conjecture,
  decl_name% GapConjecture.gap_conjecture,
  decl_name% InscribedSquare.inscribed_square_problem,
  decl_name% Bugeaud08.problem_10_8,
  decl_name% Erdos107.erdos_107,
  decl_name% BealConjecture.beal_conjecture,
  decl_name% FermatCatalanConjecture.fermat_catalan,
  decl_name% PerfectNumbers.odd_perfect_number_conjecture,
  decl_name% Jacobson.jacobson_conjecture,
  decl_name% LonelyRunnerConjecture.lonely_runner_conjecture,
  decl_name% Erdos234.erdos_234,
  decl_name% Fermat.infinite_fermat_primes,
  decl_name% PierceBirkhoff.pierce_birkhoff_conjecture,
  decl_name% Erdos1029.erdos_1029,
  decl_name% Hall.weak_hall_conjecture,
  decl_name% RudinsConjecture.rudins_conjecture,
  decl_name% Mersenne.infinitely_many_mersenne_primes,
  decl_name% Erdos572.erdos_572,
  decl_name% Transcendental.exp_add_pi_transcendental,
  decl_name% Erdos510.erdos_510,
  decl_name% Green50.green_50,
  decl_name% Erdos242.erdos_242,
  decl_name% Equidistribution.isEquidistributedModuloOne_three_halves_pow,
  decl_name% ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture_for_finite_graphs,
  decl_name% BingBorsuk.bing_borsuk_conjecture,
  decl_name% CollatzConjecture.collatz_conjecture,
  decl_name% OpenQuantumProblem23.sicPOVMs,
  decl_name% Arxiv.«math.0110202».banach_mazur_rotation_problem,
  decl_name% Erdos5.erdos_5,
  decl_name% Conjecture_1_3_to_2_3.conjecture_1_3_to_2_3,
  decl_name% FibonacciPrimes.fib_primes_infinite,
  decl_name% Singmaster.singmaster,
  decl_name% Erdos562.erdos_562,
  decl_name% Erdos564.erdos_564,
  decl_name% Arxiv.«0805.3777».isGenericRank_of_le_critical,
  decl_name% PrimeTriplets.prime_triplets,
  decl_name% Erdos212.erdos_212,
  decl_name% Idoneal.idoneal_numbers_completeness,
  decl_name% Erdos583.erdos_583,
  decl_name% Erdos233.erdos_233,
  decl_name% Bloch.blochConstant_exact_value,
  decl_name% Erdos714.erdos_714
]

end Subsets.FC100OpenSet2

open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100OpenSet2.problems [
  ("research open", 100)
]
