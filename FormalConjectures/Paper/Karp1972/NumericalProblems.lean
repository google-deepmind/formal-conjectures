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
# Five numerical and weighted formulations of P versus NP

These statements conjecture the nonexistence of deterministic polynomial-time deciders
for Karp's 0–1 integer programming, knapsack (subset-sum equality), partition,
job sequencing, and weighted max-cut problems. Integer inputs use binary encodings.
Karp's Theorem 3 explains the connection to $P \ne NP$; the completeness reductions
are not formalized here.

*Reference:* Richard M. Karp, *Reducibility among Combinatorial Problems*, in
*Complexity of Computer Computations* (1972), pp. 85–103,
https://doi.org/10.1007/978-1-4684-2001-2_9.
See §4, Theorem 3 (p. 93), and Main Theorem items 2, 18–21 (pp. 94, 95, 97).
-/

namespace Karp1972

open ComplexityTheory Computability.NumericalProblems

/-- No polynomial-time decider for 0–1 INTEGER PROGRAMMING with integer coefficients
and equality constraints (item 2, p. 94). -/
@[category research open, AMS 68 90]
theorem zeroOneProgramming_not_polytime : ¬ HasPolyTimeDecider ZeroOneProgramming := by
  sorry

/-- No polynomial-time decider for KNAPSACK in Karp's subset-sum equality formulation
over signed integers (item 18, p. 95). -/
@[category research open, AMS 11 68]
theorem subsetSum_not_polytime : ¬ HasPolyTimeDecider SubsetSum := by
  sorry

/-- No polynomial-time decider for PARTITION of an integer list into two parts
of equal sum (item 20, p. 97). -/
@[category research open, AMS 11 68]
theorem partition_not_polytime : ¬ HasPolyTimeDecider Partition := by
  sorry

/-- No polynomial-time decider for JOB SEQUENCING with positive processing times,
deadlines, penalties, and a positive upper bound on late-job penalties (item 19, p. 95). -/
@[category research open, AMS 68 90]
theorem jobSequencing_not_polytime : ¬ HasPolyTimeDecider JobSequencing := by
  sorry

/-- No polynomial-time decider for MAX CUT with signed integer edge weights and a
positive lower bound on the cut weight (item 21, p. 97). -/
@[category research open, AMS 5 68 90]
theorem weightedMaxCut_not_polytime : ¬ HasPolyTimeDecider WeightedMaxCut := by
  sorry

end Karp1972
