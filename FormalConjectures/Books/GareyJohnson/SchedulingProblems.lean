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
# Five scheduling and packing formulations of P versus NP

Each statement conjectures that an encoded finite decision problem has no uniform
deterministic polynomial-time decider in the existing TM2 model with binary encodings.

Primary reference: Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
SR1 (p. 226), SS1 (p. 236), SS14–SS15 (p. 241), SS18 (p. 242).
Theorem 4.5 (pp. 102–103) gives the strong NP-completeness proof for SS1.
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Original research background:
- Eisenbrand, Pálvölgyi, and Rothvoß, *Bin Packing via Discrepancy of Permutations*,
  arXiv:1007.2170v2 (2012), §1, pp. 1–3. Its minimum-bin formulation clarifies the
  convention that a bin budget permits unused bins.
  https://arxiv.org/abs/1007.2170v2
- Gonzalez and Sahni, *Open Shop Scheduling to Minimize Finish Time*,
  JACM 23(4) (1976), 665–679, especially the model (pp. 665–666)
  and Theorem 4.1 (pp. 675–677).
  https://doi.org/10.1145/321978.321985
- Garey, Johnson, and Sethi, *The Complexity of Flowshop and Jobshop Scheduling*,
  Mathematics of Operations Research 1(2) (1976), 117–129.
  https://doi.org/10.1287/moor.1.2.117
- Gonzalez and Sahni, *Flowshop and Jobshop Schedules: Complexity and Approximation*,
  Operations Research 26(1) (1978), 36–52. The introduction (pp. 36–38) distinguishes
  the two shop models, makespan feasibility, and binary from unary numeric encodings.
  https://www.cise.ufl.edu/~sahni/papers/flowshopAndJobshop.pdf

Bin packing permits unused bins. All schedules are nonpreemptive. SS1 has positive
durations, whereas shop durations may be zero. Flow shop allows waiting and does not
require a common job order on all machines. Job shop retains the source convention
that consecutive operations use different machines, while allowing later revisits.
Jobs in SS18 are nonempty, as in its last-operation deadline condition.

These are lower-bound conjectures. No NP-completeness reduction or equivalence to
$P \ne NP$ is formally proved here.
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.SchedulingProblems

/-- No polynomial-time decider for SR1: packing positive integer item sizes into a
positive input number of bins, each with a positive integer capacity. -/
@[category research open, AMS 68 90]
theorem binPacking_not_polytime : ¬ HasPolyTimeDecider BinPacking := by
  sorry

/-- No polynomial-time decider for SS1: scheduling positive-length tasks on one machine
within their individual release/deadline windows, without preemption. -/
@[category research open, AMS 68 90]
theorem releaseDeadline_not_polytime : ¬ HasPolyTimeDecider ReleaseDeadline := by
  sorry

/-- No polynomial-time decider for SS14: nonpreemptive open-shop scheduling with
nonnegative integer durations and a positive overall completion deadline. -/
@[category research open, AMS 68 90]
theorem openShop_not_polytime : ¬ HasPolyTimeDecider OpenShop := by
  sorry

/-- No polynomial-time decider for SS15: nonpreemptive flow-shop scheduling, with every
job visiting machines in order and finishing by a positive overall deadline. -/
@[category research open, AMS 68 90]
theorem flowShop_not_polytime : ¬ HasPolyTimeDecider FlowShop := by
  sorry

/-- No polynomial-time decider for SS18: nonpreemptive job-shop scheduling, with
job-specific machine routes and a positive overall completion deadline. -/
@[category research open, AMS 68 90]
theorem jobShop_not_polytime : ¬ HasPolyTimeDecider JobShop := by
  sorry

end GareyJohnson1979
