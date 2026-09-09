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
import FormalConjecturesTest.ForMathlib.Computability.FiniteTests

-- Transitive audit of the completed named definitions, theorems, and regression results.
#print axioms Computability.FiniteTests.Enumeration
#print axioms Computability.FiniteTests.Enumeration.monotone
#print axioms Computability.FiniteTests.Enumeration.covers
#print axioms Computability.FiniteTests.Enumeration.naturals
#print axioms Computability.FiniteTests.Enumeration.bitstringsUpTo
#print axioms Computability.FiniteTests.Enumeration.mem_bitstringsUpTo
#print axioms Computability.FiniteTests.Enumeration.bitstrings
#print axioms Computability.FiniteTests.Correct
#print axioms Computability.FiniteTests.Separation
#print axioms Computability.FiniteTests.Survives
#print axioms Computability.FiniteTests.survives
#print axioms Computability.FiniteTests.survives_eq_true
#print axioms Computability.FiniteTests.survives_iff
#print axioms Computability.FiniteTests.Survives.mono
#print axioms Computability.FiniteTests.correct_iff_survives
#print axioms Computability.FiniteTests.exists_correct_iff
#print axioms Computability.FiniteTests.separation_iff_not_exists_correct
#print axioms Computability.FiniteTests.Excludes
#print axioms Computability.FiniteTests.excludes
#print axioms Computability.FiniteTests.excludes_eq_true
#print axioms Computability.FiniteTests.Excludes.mono_input
#print axioms Computability.FiniteTests.Excludes.mono_candidate
#print axioms Computability.FiniteTests.excludes_of_empty
#print axioms Computability.FiniteTests.separation_iff_excludes
#print axioms Computability.FiniteTests.counterexampleBound
#print axioms Computability.FiniteTests.mem_counterexampleBound
#print axioms Computability.FiniteTests.counterexampleBound_spec
#print axioms Computability.FiniteTests.counterexampleBound_le
#print axioms Computability.FiniteTests.counterexampleBound_dom
#print axioms Computability.FiniteTests.counterexampleBound_partrec
#print axioms Computability.FiniteTests.counterexampleBound_total_iff
#print axioms Computability.FiniteTests.ValidCertificate
#print axioms Computability.FiniteTests.validateCertificate
#print axioms Computability.FiniteTests.validateCertificate_eq_true
#print axioms Computability.FiniteTests.ValidCertificate.excludes
#print axioms Computability.ClockedEvaluation.Clock
#print axioms Computability.ClockedEvaluation.Clock.bound
#print axioms Computability.ClockedEvaluation.Clock.bound_pos
#print axioms Computability.ClockedEvaluation.Clock.ofNat
#print axioms Computability.ClockedEvaluation.Clock.ofNat_zero
#print axioms Computability.ClockedEvaluation.Clock.ofNat_fields
#print axioms Computability.ClockedEvaluation.State
#print axioms Computability.ClockedEvaluation.Outcome
#print axioms Computability.ClockedEvaluation.run
#print axioms Computability.ClockedEvaluation.Outcome.passes
#print axioms Computability.ClockedEvaluation.Outcome.passes_eq_true
#print axioms Computability.ClockedEvaluation.checkWithin
#print axioms Computability.ClockedEvaluation.checkWithin_iff
#print axioms Computability.FiniteTests.decodeCanonical
#print axioms Computability.FiniteTests.decodeCanonical_eq_some
#print axioms Computability.FiniteTests.Enumeration.ofBitstringEncoding
#print axioms Computability.FiniteTests.ClockedCode
#print axioms Computability.FiniteTests.ClockedCode.encoded_length
#print axioms Computability.FiniteTests.Test.prefixCheck
#print axioms Computability.FiniteTests.Test.finite_fitting
#print axioms Computability.FiniteTests.Test.no_uniform_candidate
#print axioms Computability.FiniteTests.Test.excludes_prefix_iff
#print axioms Computability.FiniteTests.Test.least_bound
#print axioms Computability.FiniteTests.Test.noCandidates
#print axioms Computability.FiniteTests.Test.countdown
#print axioms Computability.FiniteTests.Test.encodedCandidate
#print axioms Computability.FiniteTests.Test.encoded_candidate_covered
