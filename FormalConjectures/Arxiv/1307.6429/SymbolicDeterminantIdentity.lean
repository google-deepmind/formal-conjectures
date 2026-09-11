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
# Symbolic determinant identity testing

*References:*
* Ivanyos, Karpinski, Qiao, and Santha,
*Generalized Wong sequences and their applications to Edmonds' problems*,
https://arxiv.org/abs/1307.6429v2, §1, pp. 1–3.

-/

namespace Arxiv.«1307.6429»

open ComplexityTheory AlgebraicProblems

/-- **Symbolic determinant identity testing** (Ivanyos et al., §1, pp. 1–3) has a
deterministic polynomial bit-time decider. Input: an explicitly row-encoded square
matrix of homogeneous linear forms, with binary integer coefficients and variable
indices. Property: its determinant is a nonzero commutative polynomial, equivalently
some integer specialization is nonsingular. Repeated coefficients add, ragged rows
are rejected, and the empty matrix is accepted (determinant one). This derandomization
conjecture imposes no rank-one or triangularizability restriction and does not ask
for noncommutative rank. -/
@[category research open, AMS 15 68]
theorem symbolicDeterminant_polytime :
    HasPolyTimeDecider SymbolicNonsingular := by
  sorry

end Arxiv.«1307.6429»
