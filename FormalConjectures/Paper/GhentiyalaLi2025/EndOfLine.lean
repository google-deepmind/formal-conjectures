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
# End-of-Line has no polynomial-time solver

*References:*
* Ghentiyala–Li, *Hierarchies within TFNP: building blocks and collapses*,
  ECCC TR25-123 revision 1, Definition 2.8, printed p. 8,
  https://eccc.weizmann.ac.il/report/2025/123/revision/1/download.
-/

namespace GhentiyalaLi2025

/-- **End-of-Line** (Ghentiyala–Li, Definition 2.8) has no deterministic polynomial-
time solver. Input: valid explicit Boolean circuits $S,P:\{0,1\}^n\to\{0,1\}^n$
with $P(0)=0$ and $S(0)\ne0$, unary arity and binary gate references. Output:
an $n$-bit $v$ with $P(S(v))\ne v$, or with $v\ne0$ and $S(P(v))\ne v$.
Zero is excluded only in the second disjunct; $n=0$ cannot satisfy the promise.
One total polynomial-time TM2 must return a valid answer on every promised input,
not necessarily an endpoint reached from zero. This PPAD lower bound implies
$P\ne NP$; the converse is unknown. -/
@[category research open, AMS 3 68]
theorem endOfLine_not_polytime : ¬
    ComplexityTheory.HasPolyTimeSolver TotalSearch.EndOfLinePromise
      TotalSearch.EndOfLineSolution := by
  sorry

end GhentiyalaLi2025
