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
# Bin packing and nonpreemptive scheduling

*References:*
- Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
  SR1 (p. 226), SS1 (p. 236), SS14–SS15 (p. 241), SS18 (p. 242),
  and Theorem 4.5 (pp. 102–103).
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Eisenbrand, Pálvölgyi, and Rothvoß, *Bin Packing via Discrepancy of Permutations*,
  arXiv:1007.2170v2 (2012), §1, pp. 1–3.
  https://arxiv.org/abs/1007.2170v2
- Gonzalez and Sahni, *Open Shop Scheduling to Minimize Finish Time*,
  JACM 23(4) (1976), 665–679, especially the model (pp. 665–666)
  and Theorem 4.1 (pp. 675–677).
  https://doi.org/10.1145/321978.321985
- Garey, Johnson, and Sethi, *The Complexity of Flowshop and Jobshop Scheduling*,
  Mathematics of Operations Research 1(2) (1976), 117–129.
  https://doi.org/10.1287/moor.1.2.117
- Gonzalez and Sahni, *Flowshop and Jobshop Schedules: Complexity and Approximation*,
  Operations Research 26(1) (1978), 36–52, introduction (pp. 36–38).
  https://www.cise.ufl.edu/~sahni/papers/flowshopAndJobshop.pdf
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.SchedulingProblems

/-- **BIN PACKING** (SR1, p. 226). Input: a list of positive integer item sizes,
a positive capacity $B$ and a positive bin budget $K$, all binary encoded. Property:
every indexed item can be assigned to one of $K$ bins with total load at most $B$ in
each bin. Unused bins and an empty item list are allowed. This problem is NP-complete,
so the nonexistence of a deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68 90]
theorem binPacking_not_polytime : ¬ HasPolyTimeDecider BinPacking := by
  sorry

/-- **SEQUENCING WITH RELEASE TIMES AND DEADLINES** (SS1, p. 236; Theorem 4.5).
Input: a list of tasks with positive processing lengths and deadlines and nonnegative
release times, all binary integers. Property: nonnegative integer start times schedule
every task without preemption on one machine, after its release and completing no later
than its deadline. Idle time and touching intervals are allowed; positive tasks cannot
overlap. This problem is NP-complete, so the nonexistence of a deterministic polynomial-time
decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68 90]
theorem releaseDeadline_not_polytime : ¬ HasPolyTimeDecider ReleaseDeadline := by
  sorry

/-- **OPEN-SHOP SCHEDULING** (SS14, p. 241; Gonzalez–Sahni 1976, Theorem 4.1).
Input: a positive machine count $m$, one row of $m$ nonnegative integer durations per job,
and a positive deadline $D$, all binary encoded. Property: nonnegative integer starts give
a nonpreemptive schedule completing by $D$, with disjoint processing intervals whenever
operations share a machine or job. Operation order is unrestricted. Zero-duration intervals
are empty and may lie inside another operation's interval, unlike the literal machine-order
clause of SS14. This processing-interval version is NP-complete, so the nonexistence of a
deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68 90]
theorem openShop_not_polytime : ¬ HasPolyTimeDecider OpenShop := by
  sorry

/-- **FLOW-SHOP SCHEDULING** (SS15, p. 241; Gonzalez–Sahni 1978, pp. 36–38).
Input: a positive machine count $m$, one row of $m$ nonnegative integer durations per job,
and a positive deadline $D$, all binary encoded. Property: a nonpreemptive integer-start
schedule completes by $D$ and visits machines in order within each job. Waiting is allowed;
job orders on different machines need not agree. Shared-machine and shared-job processing
intervals are disjoint, with zero-duration intervals empty rather than subject to SS15's
literal machine-order clause. This version is NP-complete, so the nonexistence of a
deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68 90]
theorem flowShop_not_polytime : ¬ HasPolyTimeDecider FlowShop := by
  sorry

/-- **JOB-SHOP SCHEDULING** (SS18, p. 242; Gonzalez–Sahni 1978, pp. 36–38).
Input: a positive machine count, a list of nonempty ordered jobs of machine/duration pairs,
and a positive deadline $D$, all binary encoded. Durations are nonnegative, machine indices
are in range, and consecutive operations use different machines; later revisits are allowed.
Property: a nonpreemptive integer-start schedule respects every job's order, completes by
$D$, and has disjoint processing intervals on each machine. Zero-duration intervals are
empty rather than subject to SS18's literal machine-order clause. This version is NP-complete,
so the nonexistence of a deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 68 90]
theorem jobShop_not_polytime : ¬ HasPolyTimeDecider JobShop := by
  sorry

end GareyJohnson1979
