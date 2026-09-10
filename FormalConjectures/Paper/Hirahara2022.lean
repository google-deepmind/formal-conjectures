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
# Partial minimum circuit size

Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*, FOCS 2022,
pp. 968–979; ECCC full version, Definition 8.4 and Theorem 8.5, pp. 29–30:
https://eccc.weizmann.ac.il/report/2022/119/.

The input contains all $2^n$ entries in $\{0,1,*\}$ and a unary bound $1^s$.
Only defined entries constrain the circuit. Binary AND/OR gates count toward
size, while NOT gates are free, consistent with Appendix C's size convention.
The cited NP-hardness uses randomized reductions; no deterministic
NP-completeness claim or formal reduction is asserted here.
-/

namespace Hirahara2022

/-- Does partial MCSP with the unary threshold of Definition 8.4 admit a
deterministic polynomial-time decider? -/
@[category research open, AMS 3 68]
theorem partialMinimumCircuit_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.PartialMinimumCircuit := by
  sorry

end Hirahara2022
