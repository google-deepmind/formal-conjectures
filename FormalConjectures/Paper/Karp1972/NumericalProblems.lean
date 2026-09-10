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
# Karp's numerical problems and signed-integer generalizations

*References:*
* [Ka72] Karp, R. M., *Reducibility among Combinatorial Problems*.
  In *Complexity of Computer Computations*, Plenum (1972), pp. 85–103.
  §4, Theorem 3, Main Theorem items 2, 18–21, and Appendix I, pp. 93–95, 97, 103.
  https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

namespace Karp1972

open ComplexityTheory Computability.NumericalProblems

/-- **0–1 INTEGER PROGRAMMING**, extending [Ka72], item 2, p. 94. No deterministic
polynomial-time algorithm decides whether a binary-encoded integer matrix $C$ and vector $d$
admit $x \in \{0,1\}^n$ with $Cx=d$. Columns and the right-hand side are explicit.
Here $d$ may be signed, unlike Appendix I's nonnegative-vector convention.
The extension is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 68 90]
theorem zeroOneProgramming_not_polytime : ¬ HasPolyTimeDecider ZeroOneProgramming := by
  sorry

/-- **SIGNED SUBSET SUM**, generalizing [Ka72]'s KNAPSACK, item 18, p. 95. No deterministic
polynomial-time algorithm decides whether selected positions of a binary-encoded integer list
sum to a supplied integer target. Equal entries at different positions are separate choices.
Unlike Karp's positive-integer inputs, entries and target may be zero or negative.
This extension is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 11 68]
theorem subsetSum_not_polytime : ¬ HasPolyTimeDecider SubsetSum := by
  sorry

/-- **SIGNED PARTITION**, generalizing [Ka72], item 20, p. 97. No deterministic polynomial-time
algorithm decides whether the positions of a binary-encoded integer list can be split into
two parts of equal sum. Multiplicity is retained and either part may be empty.
Unlike Karp's positive-integer lists, zero and negative entries are allowed.
This extension is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 11 68]
theorem partition_not_polytime : ¬ HasPolyTimeDecider Partition := by
  sorry

/-- **JOB SEQUENCING** ([Ka72], item 19, p. 95). No deterministic polynomial-time algorithm
decides whether a permutation of an explicit job list has total late-job penalty at most a
budget. Processing times, deadlines, penalties and budget are positive binary integers.
A job incurs its penalty exactly when its completion time exceeds its deadline.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 68 90]
theorem jobSequencing_not_polytime : ¬ HasPolyTimeDecider JobSequencing := by
  sorry

/-- **SIGNED WEIGHTED MAX CUT**, generalizing [Ka72], item 21, p. 97. No deterministic
polynomial-time algorithm decides whether a square symmetric zero-diagonal integer matrix
has a cut whose crossing weights sum to at least a positive threshold. Data are binary;
each crossing edge is counted once, and zero entries may denote missing edges.
Unlike Karp's positive edge weights, negative weights are allowed.
This extension is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68 90]
theorem weightedMaxCut_not_polytime : ¬ HasPolyTimeDecider WeightedMaxCut := by
  sorry

end Karp1972
