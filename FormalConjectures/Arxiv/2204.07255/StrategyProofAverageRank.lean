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

public import FormalConjecturesUtil

/-!
# Ortega–Klein conjecture on strategy-proof average rank

*Reference:* J. Ortega and T. Klein, *The Cost of Strategy-Proofness in School Choice*,
*Games and Economic Behavior* 141 (2023), 515–528,
[Section 6](https://arxiv.org/pdf/2204.07255#page=18).

Students' complete strict rankings and schools' priorities are independent and uniform.
This is the deterministic, order-of-growth version of the average-rank conjecture.
-/

@[expose] public section

namespace Arxiv.«2204.07255»

/--
Ortega and Klein conjecture that student-strategy-proof mechanisms cannot achieve expected
average assigned rank asymptotically smaller than $\log n$. For deterministic feasible
mechanisms, this states that no sequence has expected average rank $o(\log n)$.
The index uses market size $n+1$ to keep every market nonempty.
-/
@[category research open, AMS 60 91]
theorem strategy_proof_average_rank :
    ¬ ∃ f : (n : ℕ) → SchoolChoice.Mechanism (n + 1),
      (∀ n, SchoolChoice.StudentStrategyProof (f n)) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun n ↦ SchoolChoice.expectedAverageRank (f n))
        (fun n ↦ Real.log (n + 1)) := by
  sorry

end Arxiv.«2204.07255»
