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
# Ordinary, one-in-three and not-all-equal satisfiability

*References:*
- Thomas J. Schaefer, *The Complexity of Satisfiability Problems*, STOC (1978), pp. 216–226,
  https://doi.org/10.1145/800133.804350. See the relation framework on p. 216, Theorem 2.1
  on p. 217, and the rank-three relations $R_5$ and $R_6$ on p. 218.
- Richard M. Karp, *Reducibility among Combinatorial Problems* (1972), item 11, p. 95,
  https://doi.org/10.1007/978-1-4684-2001-2_9, for at-most-three ordinary clauses.
- Michael R. Garey and David S. Johnson, *Computers and Intractability: A Guide to the
  Theory of NP-Completeness*, W. H. Freeman (1979), LO3 and LO4, p. 259.
- Md. Manzurul Hasan, Debajyoti Mondal, and Md. Saidur Rahman,
  *Positive Planar Satisfiability Problems under 3-Connectivity Constraints* (2021),
  https://arxiv.org/abs/2108.12500, §1, pp. 1–2.
-/

namespace Schaefer1978

open ComplexityTheory Computability.BooleanSatisfiability

/-- **3-SAT** (Karp, item 11, p. 95; Schaefer, p. 216). Input: a list of clauses, each
with at most three signed literal occurrences and binary natural-number variable names.
Property: one Boolean assignment makes at least one literal true in every clause. Repetitions
are retained; an empty clause rejects, while an empty conjunction accepts. This problem is
NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent to
$P \ne NP$. -/
@[category research open, AMS 3 68]
theorem threeSat_not_polytime : ¬ HasPolyTimeDecider ThreeSat := by
  sorry

/-- **ONE-IN-THREE 3SAT** (Garey–Johnson LO4, p. 259), with occurrence-list clauses.
Input: a list of clauses with exactly three signed literal occurrences each and binary
natural-number variable names. Property: one Boolean assignment makes exactly one occurrence
true in every clause. Negations and repetitions are allowed; an empty conjunction accepts.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 3 68]
theorem oneInThree_not_polytime : ¬ HasPolyTimeDecider OneInThree := by
  sorry

/-- **POSITIVE ONE-IN-THREE SAT** (Schaefer, pp. 216, 218, relation $R_6$).
Input: a list of triples of binary natural-number variable names, with repetitions allowed
and no negations. Property: one Boolean assignment makes exactly one variable occurrence
true in every triple. An empty conjunction accepts, and there is no planarity restriction.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 3 68]
theorem positiveOneInThree_not_polytime : ¬ HasPolyTimeDecider PositiveOneInThree := by
  sorry

/-- **NOT-ALL-EQUAL 3SAT** (Garey–Johnson LO3, p. 259), with occurrence-list clauses.
Input: a list of clauses with exactly three signed literal occurrences each and binary
natural-number variable names. Property: one Boolean assignment gives every clause both a
true and a false occurrence. Negations and repetitions are allowed; an empty conjunction
accepts. This problem is NP-complete, so the nonexistence of a deterministic polynomial-time
decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 3 68]
theorem notAllEqual_not_polytime : ¬ HasPolyTimeDecider NotAllEqual := by
  sorry

/-- **POSITIVE NOT-ALL-EQUAL SAT** (Schaefer, p. 218, relation $R_5$).
Input: a list of triples of binary natural-number variable names, with repetitions allowed
and no negations. Property: one Boolean assignment gives every triple both a true and a
false variable occurrence. An empty conjunction accepts, and there is no planarity restriction.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 3 68]
theorem positiveNotAllEqual_not_polytime : ¬ HasPolyTimeDecider PositiveNotAllEqual := by
  sorry

end Schaefer1978
