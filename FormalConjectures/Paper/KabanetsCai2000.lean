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
# Minimum circuit size

- Kabanets–Cai, *Circuit Minimization Problem*, STOC 2000, pp. 73–79.
  The complete input definition appears on p. 1 of the ECCC version:
  https://eccc.weizmann.ac.il/report/1999/045/.
- Ilango, *SAT Reduces to the Minimum Circuit Size Problem with a Random Oracle*,
  §2.2, fixes the De Morgan basis and the AND/OR gate-count convention:
  https://eccc.weizmann.ac.il/report/2023/165/.

The bound is binary; the table explicitly contains all $2^n$ output bits.
The model has free NOT gates and no primitive constant gates. There are no
oracle gates, depth bounds, fan-out bounds, or uniformity conditions on witnesses.
-/

namespace KabanetsCai2000

/-- Does full-truth-table MCSP admit a deterministic polynomial-time decider?
Time is measured in the encoded table-and-bound length, not merely in the
number of variables. -/
@[category research open, AMS 3 68]
theorem minimumCircuit_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumCircuit := by
  sorry

end KabanetsCai2000
