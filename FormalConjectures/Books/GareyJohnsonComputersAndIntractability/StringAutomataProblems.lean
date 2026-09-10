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
# Common strings, DFA intersection and DFA inference

*References:*
- Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
  SR8–SR10 (p. 228), AL6 (p. 266), and AL8 (p. 267).
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Maier, *The Complexity of Some Problems on Subsequences and Supersequences*,
  JACM 25(2) (1978), 322–336, §1 and Theorems 1 and 4.
  https://doi.org/10.1145/322063.322075
- Gallant, Maier, and Storer, *On Finding Minimal Length Superstrings*,
  JCSS 20(1) (1980), 50–58.
  https://doi.org/10.1016/0022-0000(80)90004-5
- Kozen, *Lower Bounds for Natural Proof Systems*, FOCS 1977, 254–266:
  Definition 3.2.2 and Lemma 3.2.3, pp. 261–262.
  https://www.cs.cornell.edu/kozen/Papers/LowerBounds.pdf
- Gold, *Complexity of Automaton Identification from Given Data*,
  Information and Control 37(3) (1978), 302–320.
  https://doi.org/10.1016/S0019-9958(78)90562-4
- Lingg, de Oliveira Oliveira, and Wolf, *Learning from Positive and Negative
  Examples: New Proof for Binary Alphabets*, IPL 183 (2024), 106427,
  Definition 1, Theorem 2, and §4; preprint arXiv:2206.10025v1.
  https://doi.org/10.1016/j.ipl.2023.106427
  https://arxiv.org/abs/2206.10025v1
- Chalermsook, Laekhanukit, and Nanongkai, *Pre-Reduction Graph Products:
  Hardnesses of Properly Learning DFAs and Approximating EDP on DAGs* (2014),
  §1.2.1 and §§3.1–3.2.
  https://eprints.cs.univie.ac.at/4105/1/main_focs2014_dfa.pdf
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.StringProblems Computability.AutomataProblems

/-- **SHORTEST COMMON SUPERSEQUENCE** (SR8, p. 228; Maier, Theorem 4).
Input: a finite alphabet size, an arbitrary-length list of words using in-range symbol
indices, and a positive length bound $K$, all binary encoded. Property: some word of length
at most $K$ contains every input word as a subsequence, allowing arbitrary deletions.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 68]
theorem commonSupersequence_not_polytime : ¬ HasPolyTimeDecider CommonSupersequence := by
  sorry

/-- **SHORTEST COMMON SUPERSTRING** (SR9, p. 228). Input: a finite alphabet size,
an arbitrary-length list of words using in-range symbol indices, and a positive length
bound $K$, all binary encoded. Property: some word of length at most $K$ contains every
input word as a contiguous substring; overlapping occurrences are allowed. This problem
is NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 68]
theorem commonSuperstring_not_polytime : ¬ HasPolyTimeDecider CommonSuperstring := by
  sorry

/-- **LONGEST COMMON SUBSEQUENCE** (SR10, p. 228; Maier, Theorem 1).
Input: a finite alphabet size, an arbitrary-length list of words using in-range symbol
indices, and a positive threshold $K$, all binary encoded. Property: a word of length
at least $K$ is a subsequence of every input word. The represented length-$K$ witness is
equivalent by truncation. This problem is NP-complete, so the nonexistence of a deterministic
polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68]
theorem commonSubsequence_not_polytime : ¬ HasPolyTimeDecider CommonSubsequence := by
  sorry

/-- **FINITE STATE AUTOMATA INTERSECTION** (AL6, p. 266; Kozen, Lemma 3.2.3).
Input: a common finite alphabet size and an input-sized list of total DFA transition
tables, initial states and accepting flags, all binary encoded. Property: one word is
accepted by every DFA. No polynomial word-length bound is imposed; an empty family accepts.
This problem is PSPACE-complete, so the nonexistence of a deterministic polynomial-time
decider is equivalent to $P\ne\mathrm{PSPACE}$. It follows from $P\ne NP$; the converse
implication is not known. -/
@[category research open, AMS 68]
theorem dfaIntersection_not_polytime : ¬ HasPolyTimeDecider DFAIntersection := by
  sorry

/-- **MINIMUM INFERRED FINITE STATE AUTOMATON** (AL8, p. 267;
Lingg–de Oliveira Oliveira–Wolf, Definition 1 and Theorem 2). Input: a finite alphabet size,
lists of positive and negative sample words with in-range symbol indices, and a positive
state bound $K$, all binary encoded. Property: a total $K$-state DFA accepts all positive
samples and rejects all negative samples. Unreachable states are permitted, making exactly
$K$ equivalent to at most $K$; other words are unconstrained. This accepting-state problem
is NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 68]
theorem inferredDFA_not_polytime : ¬ HasPolyTimeDecider InferredDFA := by
  sorry

end GareyJohnson1979
