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
import FormalConjecturesUtil

/-!
# Five string and automata polynomial-time lower-bound formulations

Primary reference: Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
SR8–SR10 (p. 228), AL6 (p. 266), and AL8 (p. 267).
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Research background:
- Maier, *The Complexity of Some Problems on Subsequences and Supersequences*,
  JACM 25(2) (1978), 322–336: §1 and Theorems 1 and 4 give the general-alphabet
  LCS and SCS decision problems and their NP-completeness.
  https://doi.org/10.1145/322063.322075
- Gallant, Maier, and Storer, *On Finding Minimal Length Superstrings*,
  JCSS 20(1) (1980), 50–58, studies substring containment and its complexity.
  SR9 cites the earlier Maier–Storer 1977 report.
  https://doi.org/10.1016/0022-0000(80)90004-5
- Kozen, *Lower Bounds for Natural Proof Systems*, FOCS 1977, 254–266:
  Definition 3.2.2 and Lemma 3.2.3, pp. 261–262, establish PSPACE-completeness
  of intersection nonemptiness for an input-sized family of DFAs.
  https://www.cs.cornell.edu/kozen/Papers/LowerBounds.pdf
- Gold, *Complexity of Automaton Identification from Given Data*,
  Information and Control 37(3) (1978), 302–320.
  AL8 cites a 1974 unpublished manuscript with the same title (bibliography p. 301).
  Its Mealy-machine model must not be conflated with accepting-state DFAs.
  https://doi.org/10.1016/S0019-9958(78)90562-4
- Lingg, de Oliveira Oliveira, and Wolf, *Learning from Positive and Negative
  Examples: New Proof for Binary Alphabets*, IPL 183 (2024), 106427:
  Definition 1 and Theorem 2 give the accepting-state DFA problem and its hardness;
  §4 explains the distinction from Gold's model. The preprint is arXiv:2206.10025v1.
  https://doi.org/10.1016/j.ipl.2023.106427
  https://arxiv.org/abs/2206.10025v1
- Chalermsook, Laekhanukit, and Nanongkai, *Pre-Reduction Graph Products:
  Hardnesses of Properly Learning DFAs and Approximating EDP on DAGs* (2014),
  §1.2.1 and §§3.1–3.2, connect minimum consistent DFAs to learning and approximation.
  https://eprints.cs.univie.ac.at/4105/1/main_focs2014_dfa.pdf

All five statements use binary-encoded finite inputs and the existing TM2 model.
The string collection and automaton family sizes are part of the input.
Subsequences allow arbitrary deletions; substrings must be contiguous.
Inference asks for a K-state DFA, allowing unreachable states and requiring
agreement only on the supplied positive and negative samples.

The four NP-complete problems motivate P-versus-NP formulations. DFA intersection
is PSPACE-complete: its conjectured lower bound must not be described as an
equivalence to $P \ne NP$. No completeness reductions or complexity-class
equivalences are formally proved here.
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.StringProblems Computability.AutomataProblems

/-- No polynomial-time decider for SR8: a common supersequence of length at most
a positive input threshold, over an input finite alphabet. -/
@[category research open, AMS 68]
theorem commonSupersequence_not_polytime : ¬ HasPolyTimeDecider CommonSupersequence := by
  sorry

/-- No polynomial-time decider for SR9: a string of length at most a positive
input threshold containing every input string as a contiguous substring. -/
@[category research open, AMS 68]
theorem commonSuperstring_not_polytime : ¬ HasPolyTimeDecider CommonSuperstring := by
  sorry

/-- No polynomial-time decider for SR10: a subsequence common to all input strings
whose length is at least a positive input threshold. -/
@[category research open, AMS 68]
theorem commonSubsequence_not_polytime : ¬ HasPolyTimeDecider CommonSubsequence := by
  sorry

/-- No polynomial-time decider for AL6: nonemptiness of the intersection of the
languages accepted by an input-sized family of DFAs over a common finite alphabet. -/
@[category research open, AMS 68]
theorem dfaIntersection_not_polytime : ¬ HasPolyTimeDecider DFAIntersection := by
  sorry

/-- No polynomial-time decider for AL8: existence of a K-state DFA accepting all
positive samples and rejecting all negative samples, for positive input K. -/
@[category research open, AMS 68]
theorem inferredDFA_not_polytime : ¬ HasPolyTimeDecider InferredDFA := by
  sorry

end GareyJohnson1979
