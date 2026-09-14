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

*References:*
* Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*, FOCS 2022,
  pp. 968–979; ECCC full version, Definition 8.4 and Theorem 8.5, pp. 29–30,
  Appendix C, https://eccc.weizmann.ac.il/report/2022/119/.
-/

namespace Hirahara2022

/-- **Partial MCSP** (Hirahara, Definition 8.4) has no deterministic polynomial
bit-time decider. Input: binary arity $n$, all $2^n$ entries in $\{0,1,*\}$, and a
unary bound $1^s$. Property: a circuit with at most $s$ AND/OR gates agrees at every
defined entry; NOT gates are free. Incorrect table lengths are rejected. There are
no primitive constants, so $n=0$ has no witnesses. Unary and binary bounds are
polynomially equivalent after capping at a full-table realization bound.
Theorem 8.5 gives randomized-reduction hardness: $NP\not\subseteq BPP$ implies
this lower bound; $P\ne NP$ alone is not the cited sufficient assumption. -/
@[category research open, AMS 68]
theorem partialMinimumCircuit_not_polytime : ¬
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.PartialMinimumCircuit := by
  sorry

end Hirahara2022
